from __future__ import annotations
import os
import re
from enum import Enum
from typing import List, Dict


class CodeType(Enum):
    MISC = 0  # miscellaneous, should be ignore
    LABEL = 1
    OP = 2  # operation


class OpType(Enum):
    PUSH = 1
    MOV = 2
    SUB = 3
    ADD = 4
    POP = 5
    RET = 6
    SAL = 7  # shift arithmetic left
    CDQ = 8  # edx = eax
    IDIV = 9
    IMUL = 10
    CALL = 11
    LEA = 12  # load effective address
    CMP = 13
    JG = 14
    JMP = 15
    JNE = 16
    JNS = 17
    NOP = 18
    JLE = 19
    JS = 20
    JGE = 21
    JL = 21



class Address:
    def __init__(self, raw_str: str) -> None:
        result = re.search(r"[\-]{0,1}[\d]*\[.+\]", raw_str)
        address_str = result.group(0)
        offset_result = re.search(r"-{0,1}\d+", address_str)
        if offset_result != None:
            self.offset = int(offset_result.group(0))
        else:
            self.offset = 0
        operand_result = re.search(r"\[(.+)\]", address_str)
        self.operand = operand_result.group(1)

    def __str__(self) -> str:
        return f"offset: {self.offset}, operand: {self.operand}"


class ArrayAddress:
    def __init__(self, raw_str: str) -> None:
        result = re.search(r"[\-]{0,1}[\d]*\[.+\]", raw_str)
        address_str = result.group(0)
        offset_result = re.search(r"-{0,1}\d+", address_str)
        if offset_result != None:
            self.offset = int(offset_result.group(0))
        else:
            self.offset = 0
        operand_result = re.search(r"\[(\w+)\+(\w+)\*4\]", address_str)
        self.operand1 = operand_result.group(1)
        self.operand2 = operand_result.group(2)

    def __str__(self) -> str:
        return f"offset: {self.offset}, operand: {self.operand1, self.operand2}"


class Operation:
    def __init__(self, raw_str: str) -> None:
        self.operand_list: List[str | int | Address] = []

        if "push" in raw_str:
            if "[" in raw_str:
                raise Exception(raw_str)
            self.type = OpType.PUSH
            result = re.search(r"(\bpush\b)\s+(\b\w+)", raw_str)
            self.operand_list = [result.group(2)]

        elif "call" in raw_str:
            if "[" in raw_str:
                raise Exception(raw_str)
            self.type = OpType.CALL
            result = re.search(r"\bcall\b\s+(\b\w+)", raw_str)
            self.operand_list = [result.group(1)]

        elif "jge" in raw_str:
            if "[" in raw_str:
                raise Exception(raw_str)
            self.type = OpType.JGE
            result = re.search(r"\bjge\b\s+([\w\.]+)", raw_str)
            self.operand_list = [result.group(1)]

        elif "jg" in raw_str:
            if "[" in raw_str:
                raise Exception(raw_str)
            self.type = OpType.JG
            result = re.search(r"\bjg\b\s+([\w\.]+)", raw_str)
            self.operand_list = [result.group(1)]

        elif "jmp" in raw_str:
            if "[" in raw_str:
                raise Exception(raw_str)
            self.type = OpType.JMP
            result = re.search(r"\bjmp\b\s+([\w\.]+)", raw_str)
            self.operand_list = [result.group(1)]

        elif "jne" in raw_str:
            if "[" in raw_str:
                raise Exception(raw_str)
            self.type = OpType.JNE
            result = re.search(r"\bjne\b\s+([\w\.]+)", raw_str)
            self.operand_list = [result.group(1)]

        elif "jns" in raw_str:
            if "[" in raw_str:
                raise Exception(raw_str)
            self.type = OpType.JNS
            result = re.search(r"\bjns\b\s+([\w\.]+)", raw_str)
            self.operand_list = [result.group(1)]

        elif "jle" in raw_str:
            if "[" in raw_str:
                raise Exception(raw_str)
            self.type = OpType.JLE
            result = re.search(r"\bjle\b\s+([\w\.]+)", raw_str)
            self.operand_list = [result.group(1)]

        elif "jl" in raw_str:
            if "[" in raw_str:
                raise Exception(raw_str)
            self.type = OpType.JL
            result = re.search(r"\bjl\b\s+([\w\.]+)", raw_str)
            self.operand_list = [result.group(1)]

        elif "js" in raw_str:
            if "[" in raw_str:
                raise Exception(raw_str)
            self.type = OpType.JS
            result = re.search(r"\bjs\b\s+([\w\.]+)", raw_str)
            self.operand_list = [result.group(1)]

        elif "mov" in raw_str:
            self.type = OpType.MOV
            raw_str = raw_str.replace("rax", "eax")
            result = re.search(r"(\bmov\b)\s+(\b.+),\s+(\b.+)", raw_str)
            for i in range(2, 4):
                operand_str = result.group(i)
                if "[" in operand_str:
                    if "*" not in operand_str:
                        self.operand_list.append(Address(operand_str))
                    else:
                        self.operand_list.append(ArrayAddress(operand_str))
                elif operand_str.lstrip("-").isdigit():
                    self.operand_list.append(int(operand_str))
                else:
                    self.operand_list.append(operand_str)

        elif "idiv" in raw_str:
            self.type = OpType.IDIV
            result = re.search(r"idiv\s+(\b.+)", raw_str)
            operand_str = result.group(1)
            if "[" in operand_str:
                self.operand_list.append(Address(operand_str))
            elif operand_str.lstrip("-").isdigit():
                raise Exception
                self.operand_list.append(int(operand_str))
            else:
                self.operand_list.append(operand_str)

        elif "imul" in raw_str:
            self.type = OpType.IMUL
            result = re.search(r"\bimul\b\s+(\b.+),\s+(\b.+),\s+(\b.+)", raw_str)
            para_num = 3
            if result == None:
                result = re.search(r"\bimul\b\s+(\b.+),\s+(\b.+)", raw_str)
                para_num = 2
            for i in range(1, 1 + para_num):
                operand_str = result.group(i)
                if "[" in operand_str:
                    self.operand_list.append(Address(operand_str))
                elif operand_str.lstrip("-").isdigit():
                    self.operand_list.append(int(operand_str))
                else:
                    self.operand_list.append(operand_str)

        elif "sub" in raw_str:
            self.type = OpType.SUB
            result = re.search(r"\bsub\b\s+(\b.+),\s+(\b.+)", raw_str)
            for i in range(1, 3):
                operand_str = result.group(i)
                if "[" in operand_str:
                    self.operand_list.append(Address(operand_str))
                elif operand_str.isdigit():
                    self.operand_list.append(int(operand_str))
                else:
                    self.operand_list.append(operand_str)

        elif "add" in raw_str:
            self.type = OpType.ADD
            result = re.search(r"\badd\b\s+(\b.+),\s+(\b.+)", raw_str)
            for i in range(1, 3):
                operand_str = result.group(i)
                if "[" in operand_str:
                    self.operand_list.append(Address(operand_str))
                elif operand_str.isdigit():
                    self.operand_list.append(int(operand_str))
                else:
                    self.operand_list.append(operand_str)

        elif "sal" in raw_str:
            if "[" in raw_str:
                raise Exception(raw_str)
            self.type = OpType.SAL
            result = re.search(r"sal\s+(\w+),\s+([\w]+)", raw_str)
            for i in range(1, 3):
                operand_str = result.group(i)
                if operand_str.isdigit():
                    self.operand_list.append(int(operand_str))
                else:
                    self.operand_list.append(operand_str)

        elif "lea" in raw_str:
            self.type = OpType.LEA
            result = re.search(r"\blea\b\s+(.+),\s+(.+)", raw_str)
            for i in range(1, 3):
                operand_str = result.group(i)
                operand_str = operand_str.replace("rdx", "edx")
                operand_str = operand_str.replace("rax", "eax")
                if "[" in operand_str:
                    self.operand_list.append(Address(operand_str))
                elif operand_str.isdigit():
                    raise Exception(operand_str)
                else:
                    self.operand_list.append(operand_str)

        elif "cmp" in raw_str:
            self.type = OpType.CMP
            result = re.search(r"\bcmp\b\s+(\b.+),\s+(\b.+)", raw_str)
            for i in range(1, 3):
                operand_str = result.group(i)
                if "[" in operand_str:
                    self.operand_list.append(Address(operand_str))
                elif operand_str.isdigit():
                    self.operand_list.append(int(operand_str))
                else:
                    self.operand_list.append(operand_str)

        elif "pop" in raw_str:
            if "[" in raw_str:
                raise Exception(raw_str)
            self.type = OpType.POP
            result = re.search(r"pop\s+(\w+)", raw_str)
            self.operand_list.append(result.group(1))

        elif "ret" in raw_str:
            self.type = OpType.RET

        elif "cdq" in raw_str:
            self.type = OpType.CDQ

        elif "nop" in raw_str:
            self.type = OpType.NOP

        else:
            raise Exception(raw_str)


class Code:
    def __init__(self, raw_str: str) -> None:
        self.raw_str = raw_str
        if ":" in raw_str and '"' not in raw_str:
            self.type = CodeType.LABEL
            self.label_str = raw_str.rstrip(":")

        elif raw_str[0] == ".":
            self.type = CodeType.MISC
        else:
            self.type = CodeType.OP
            self.operation = Operation(raw_str)

    def print(self) -> None:
        match self.type:
            case CodeType.LABEL:
                print(self.type, self.raw_str)
                print(" ", self.label_str)

            case CodeType.OP:
                print(self.type, self.operation.type, self.raw_str)
                match self.operation.type:
                    case OpType.PUSH:
                        print(" ", self.operation.operand_list)

                    case OpType.CALL:
                        print(" ", self.operation.operand_list)

                    case OpType.JG:
                        print(" ", self.operation.operand_list)

                    case OpType.JGE:
                        print(" ", self.operation.operand_list)

                    case OpType.JMP:
                        print(" ", self.operation.operand_list)

                    case OpType.JNE:
                        print(" ", self.operation.operand_list)

                    case OpType.JNS:
                        print(" ", self.operation.operand_list)

                    case OpType.JLE:
                        print(" ", self.operation.operand_list)

                    case OpType.JS:
                        print(" ", self.operation.operand_list)

                    case OpType.MOV:
                        print(
                            " ",
                            [
                                str(i)
                                if isinstance(i, Address) or isinstance(i, ArrayAddress)
                                else i
                                for i in self.operation.operand_list
                            ],
                        )

                    case OpType.LEA:
                        print(
                            " ",
                            [
                                str(i) if isinstance(i, Address) else i
                                for i in self.operation.operand_list
                            ],
                        )

                    case OpType.CMP:
                        print(
                            " ",
                            [
                                str(i) if isinstance(i, Address) else i
                                for i in self.operation.operand_list
                            ],
                        )

                    case OpType.IDIV:
                        print(
                            " ",
                            [
                                str(i) if isinstance(i, Address) else i
                                for i in self.operation.operand_list
                            ],
                        )

                    case OpType.IMUL:
                        print(
                            " ",
                            [
                                str(i) if isinstance(i, Address) else i
                                for i in self.operation.operand_list
                            ],
                        )

                    case OpType.SUB:
                        print(
                            " ",
                            [
                                str(i) if isinstance(i, Address) else i
                                for i in self.operation.operand_list
                            ],
                        )

                    case OpType.ADD:
                        print(
                            " ",
                            [
                                str(i) if isinstance(i, Address) else i
                                for i in self.operation.operand_list
                            ],
                        )

                    case OpType.SAL:
                        print(" ", self.operation.operand_list)

                    case OpType.POP:
                        print(" ", self.operation.operand_list)

                    case OpType.CDQ:
                        print(" ", self.operation.operand_list)

                    case OpType.RET:
                        print(" ", self.operation.operand_list)

                    case OpType.NOP:
                        print(" ", self.operation.operand_list)

                    case _:
                        raise Exception(self.operation.type)

            case _:
                raise Exception


class Parser:
    def __init__(self, c_file_path: str) -> None:
        # convert c code into assembly
        dot_loc = c_file_path.rfind(".")
        assembly_path = c_file_path[:dot_loc] + ".s"
        command = (
            f"gcc -S -fverbose-asm -masm=intel -O0 {c_file_path} -o {assembly_path}"
        )
        os.system(command)

        # load assembly code
        with open(assembly_path, "r") as file:
            # ignore comment
            self.assembly_str_list = re.sub("#.*\n", "\n", file.read()).split("\n")
            # remove spaces
            self.assembly_str_list = [i.strip() for i in self.assembly_str_list]
            # remove empty str
            self.assembly_str_list = list(
                filter(lambda a: a != "", self.assembly_str_list)
            )
            # replace rbx to ebx
            self.assembly_str_list = [
                i.replace("rbx", "ebx") for i in self.assembly_str_list
            ]

        self.code_list: List[Code] = []
        for code_str in self.assembly_str_list:
            tmp_code = Code(code_str)
            if tmp_code.type != CodeType.MISC:
                self.code_list.append(tmp_code)
        '''
        for code in self.code_list:
            code.print()
        '''

        self.label_dict: Dict[str, int] = {}
        self.operation_list: List[Code] = []
        for code in self.code_list:
            if code.type == CodeType.LABEL:
                self.label_dict[code.label_str] = len(self.operation_list)
            else:
                self.operation_list.append(code)
        '''
        # record the location of the label
        print("----complete code----")
        print()
        for i in range(len(self.operation_list)):
            if i in self.label_dict.values():
                for label in self.label_dict.keys():
                    if self.label_dict[label] == i:
                        print(f"---{label}---")
            self.operation_list[i].print()
        '''

        # save operation
        with open("./tmp.s", "w") as f:
            for operation in self.operation_list:
                f.write(operation.raw_str + "\n")


# test code
if __name__ == "__main__":
    parser = Parser("array.c")
