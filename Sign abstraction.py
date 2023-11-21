from __future__ import annotations
from getfiles import Parser, OpType, Address, ArrayAddress
from typing import List, Dict, Union, Tuple, Set
from enum import Enum
import time
from z3 import ArithRef, BoolRef, Not, And, Solver, Int, simplify, IntNumRef, sat


class AbstractMode(Enum):
    ANY_INT = "Any Int"
    SIGN = "Sign"


ABSTRACT_MODE = AbstractMode.SIGN


class AbstractType(Enum):
    ERROR = "ERROR"
    ANY_INT = "Any Int"  # any int value
    POSITIVE_INT = "Positive Int"  # positive int
    NEGATIVE_INT = "Negative Int"  # negative int
    ZERO = "Zero"  # not zero
    Int = "Int"
    Finish = "Finish"


class ExceptionType(Enum):
    ARITHMETIC_EXCEPTION = "Arithmetic Exception"


class Sign_abstraction:
    def __init__(
            self, variable: AbstractType | int, memory_id: None | int = None
    ) -> None:
        self.memory_id = memory_id  # the index in the memory
        if isinstance(variable, AbstractType):
            self.type = variable
            self.value = None
        elif isinstance(variable, int):
            if variable>0:
               self.type = AbstractType.POSITIVE_INT
            elif variable<0:
                self.type=AbstractType.NEGATIVE_INT
            elif variable==0:
                self.type=AbstractType.ZERO

    def __str__(self) -> str:
        return f"{str(self.type)}"

    def __add__(self, b: Sign_abstraction) -> Sign_abstraction:
        match self.type:
            case AbstractType.ANY_INT:
                match b.type:
                    case AbstractType.ANY_INT | AbstractType.POSITIVE_INT | AbstractType.NEGATIVE_INT | AbstractType.ZERO | AbstractType.Int:
                        return Sign_abstraction(AbstractType.ANY_INT)
            case AbstractType.NEGATIVE_INT:
                match b.type:
                    case AbstractType.POSITIVE_INT:
                        return Sign_abstraction(AbstractType.ANY_INT)
                    case AbstractType.NEGATIVE_INT:
                        return Sign_abstraction(AbstractType.NEGATIVE_INT)
                    case AbstractType.ZERO | AbstractType.Int:
                        return Sign_abstraction(AbstractType.NEGATIVE_INT)
                    case AbstractType.ANY_INT:
                        return Sign_abstraction(AbstractType.ANY_INT)
            case AbstractType.POSITIVE_INT:
                match b.type:
                    case AbstractType.POSITIVE_INT:
                        return Sign_abstraction(AbstractType.POSITIVE_INT)
                    case AbstractType.NEGATIVE_INT:
                        return Sign_abstraction(AbstractType.ANY_INT)
                    case AbstractType.ZERO | AbstractType.Int:
                        return Sign_abstraction(AbstractType.POSITIVE_INT)
                    case AbstractType.ANY_INT:
                        return Sign_abstraction(AbstractType.ANY_INT)
            case AbstractType.ZERO:
                match b.type:
                    case AbstractType.POSITIVE_INT:
                        return Sign_abstraction(AbstractType.POSITIVE_INT)
                    case AbstractType.NEGATIVE_INT:
                        return Sign_abstraction(AbstractType.NEGATIVE_INT)
                    case AbstractType.ZERO:
                        return Sign_abstraction(AbstractType.ZERO)
                    case AbstractType.ANY_INT:
                        return Sign_abstraction(AbstractType.ANY_INT)
                    case AbstractType.Int:
                        if b.value > 0:
                            return Sign_abstraction(AbstractType.POSITIVE_INT)
                        if b.value < 0:
                            return Sign_abstraction(AbstractType.NEGATIVE_INT)
                        if b.value == 0:
                            return Sign_abstraction(AbstractType.ZERO)
            case AbstractType.Int:
                match b.type:
                    case AbstractType.POSITIVE_INT:
                        return Sign_abstraction(AbstractType.POSITIVE_INT)
                    case AbstractType.NEGATIVE_INT:
                        return Sign_abstraction(AbstractType.NEGATIVE_INT)
                    case AbstractType.ANY_INT:
                        return Sign_abstraction(AbstractType.ANY_INT)
                    case AbstractType.Int | AbstractType.ZERO:
                        return Sign_abstraction(self.value + b.value)

    def __sub__(self, b: Sign_abstraction) -> Sign_abstraction:
        match self.type:
            case AbstractType.ANY_INT:
                match b.type:
                    case (AbstractType.ANY_INT | AbstractType.POSITIVE_INT | AbstractType.NEGATIVE_INT
                          | AbstractType.ZERO | AbstractType.Int):
                        return Sign_abstraction(AbstractType.ANY_INT)
            case AbstractType.NEGATIVE_INT:
                match b.type:
                    case AbstractType.POSITIVE_INT:
                        return Sign_abstraction(AbstractType.NEGATIVE_INT)
                    case AbstractType.NEGATIVE_INT:
                        return Sign_abstraction(AbstractType.ANY_INT)
                    case AbstractType.ZERO | AbstractType.Int:
                        return Sign_abstraction(AbstractType.NEGATIVE_INT)
                    case AbstractType.ANY_INT:
                        return Sign_abstraction(AbstractType.ANY_INT)
            case AbstractType.POSITIVE_INT:
                match b.type:
                    case AbstractType.POSITIVE_INT:
                        return Sign_abstraction(AbstractType.ANY_INT)
                    case AbstractType.NEGATIVE_INT:
                        return Sign_abstraction(AbstractType.POSITIVE_INT)
                    case AbstractType.ZERO | AbstractType.Int:
                        return Sign_abstraction(AbstractType.POSITIVE_INT)
                    case AbstractType.ANY_INT:
                        return Sign_abstraction(AbstractType.ANY_INT)
            case AbstractType.ZERO:
                match b.type:
                    case AbstractType.POSITIVE_INT:
                        return Sign_abstraction(AbstractType.NEGATIVE_INT)
                    case AbstractType.NEGATIVE_INT:
                        return Sign_abstraction(AbstractType.POSITIVE_INT)
                    case AbstractType.ZERO:
                        return Sign_abstraction(AbstractType.ZERO)
                    case AbstractType.ANY_INT:
                        return Sign_abstraction(AbstractType.ANY_INT)
                    case AbstractType.Int:
                        if b.value > 0:
                            return Sign_abstraction(AbstractType.NEGATIVE_INT)
                        if b.value < 0:
                            return Sign_abstraction(AbstractType.POSITIVE_INT)
                        if b.value == 0:
                            return Sign_abstraction(AbstractType.ZERO)
            case AbstractType.Int:
                match b.type:
                    case AbstractType.POSITIVE_INT:
                        return Sign_abstraction(AbstractType.NEGATIVE_INT)
                    case AbstractType.NEGATIVE_INT:
                        return Sign_abstraction(AbstractType.POSITIVE_INT)
                    case AbstractType.ANY_INT:
                        return Sign_abstraction(AbstractType.ANY_INT)
                    case AbstractType.Int | AbstractType.ZERO:
                        return Sign_abstraction(self.value - b.value)

    def __mov__(self, b: Sign_abstraction) -> Sign_abstraction:
        match b.type:
            case AbstractType.POSITIVE_INT:
                return Sign_abstraction(AbstractType.POSITIVE_INT)
            case AbstractType.NEGATIVE_INT:
                return Sign_abstraction(AbstractType.NEGATIVE_INT)
            case AbstractType.ZERO:
                return Sign_abstraction(AbstractType.ZERO)
            case AbstractType.ANY_INT:
                return Sign_abstraction(AbstractType.ANY_INT)
            case AbstractType.Int:
                self.value = b.value
                return Sign_abstraction(AbstractType.Int)

    def __idiv__(self, b: Sign_abstraction) -> Sign_abstraction:
        if not isinstance(b, Sign_abstraction):
            raise Exception
        if b.type==AbstractType.ZERO:
            print("DIVIDE BY ZERO")
            return Sign_abstraction(AbstractType.ERROR)
        match self.type:
            case AbstractType.ANY_INT:
                match b.type:
                    case AbstractType.ANY_INT | AbstractType.POSITIVE_INT | AbstractType.NEGATIVE_INT:
                        return Sign_abstraction(AbstractType.ANY_INT)
            case AbstractType.NEGATIVE_INT:
                match b.type:
                    case AbstractType.POSITIVE_INT:
                        return Sign_abstraction(AbstractType.NEGATIVE_INT)
                    case AbstractType.NEGATIVE_INT:
                        return Sign_abstraction(AbstractType.POSITIVE_INT)
            case AbstractType.ANY_INT:
                return Sign_abstraction(AbstractType.ANY_INT)
            case AbstractType.POSITIVE_INT:
                match b.type:
                    case AbstractType.POSITIVE_INT:
                        return Sign_abstraction(AbstractType.POSITIVE_INT)
                    case AbstractType.NEGATIVE_INT:
                        return Sign_abstraction(AbstractType.NEGATIVE_INT)
                    case AbstractType.ANY_INT:
                        return Sign_abstraction(AbstractType.ANY_INT)
            case AbstractType.ZERO:
                match b.type:
                    case AbstractType.POSITIVE_INT | AbstractType.NEGATIVE_INT | AbstractType.ANY_INT:
                        return Sign_abstraction(AbstractType.ZERO)
            case _:
                raise Exception(self.type)

    def __imul__(self, b: Sign_abstraction) -> Sign_abstraction:
        if not isinstance(b, Sign_abstraction):
            raise Exception
        match self.type:
            case AbstractType.ANY_INT:
                match b.type:
                    case AbstractType.ANY_INT | AbstractType.POSITIVE_INT | AbstractType.NEGATIVE_INT:
                        return Sign_abstraction(AbstractType.ANY_INT)
                    case AbstractType.ZERO:
                        return Sign_abstraction(AbstractType.ZERO)
            case AbstractType.NEGATIVE_INT:
                match b.type:
                    case AbstractType.POSITIVE_INT:
                        return Sign_abstraction(AbstractType.NEGATIVE_INT)
                    case AbstractType.NEGATIVE_INT:
                        return Sign_abstraction(AbstractType.POSITIVE_INT)
                    case AbstractType.ZERO:
                        return Sign_abstraction(AbstractType.ZERO)
                    case AbstractType.ANY_INT:
                        return Sign_abstraction(AbstractType.ANY_INT)
            case AbstractType.POSITIVE_INT:
                match b.type:
                    case AbstractType.POSITIVE_INT:
                        return Sign_abstraction(AbstractType.POSITIVE_INT)
                    case AbstractType.NEGATIVE_INT:
                        return Sign_abstraction(AbstractType.NEGATIVE_INT)
                    case AbstractType.ZERO:
                        return Sign_abstraction(AbstractType.ZERO)
                    case AbstractType.ANY_INT:
                        return Sign_abstraction(AbstractType.ANY_INT)
            case AbstractType.ZERO:
                match b.type:
                    case AbstractType.POSITIVE_INT | AbstractType.NEGATIVE_INT | AbstractType.ANY_INT | AbstractType.ZERO:
                        return Sign_abstraction(AbstractType.ZERO)
            case _:
                raise Exception(self.type)


class Abstractexecutor:
    def __init__(self, parser: Parser) -> None:
        self.parser = parser
        self.register_dict: Dict[str, AbstractType | None | int] = {}
        self.memory_array: List[None | Sign_abstraction] = [None] * 10_000
        self.register_dict["ret"] = None
        self.register_dict["rsp"] = 9000
        self.register_dict["rbp"] = 9000
        self.register_dict["eax"] = None
        self.register_dict["ebx"] = None
        self.register_dict["ecx"] = AbstractType.ANY_INT
        self.register_dict["edx"] = AbstractType.ANY_INT
        self.register_dict["r8d"] = AbstractType.ANY_INT
        self.register_dict["r9d"] = AbstractType.ANY_INT
        self.compare = None
        for i in range(4, 84):
            self.memory_array[
                self.register_dict["rsp"] + 8 * (i + 1)
                ] = AbstractType.ANY_INT

    def run(self, label_name: str, operation, operation_index,limit_time) -> AbstractType | int | None:
        '''
        parameter_list: List[Sign_abstraction] = []
        for i in range(len(para_list)):
            parameter_list.append(Sign_abstraction(para_list[i]))
        para_len = len(parameter_list)
        if para_len >= 1:
            self.register_dict["ecx"] = AbstractType.ANY_INT
        if para_len >= 2:
            self.register_dict["edx"] = AbstractType.ANY_INT
        if para_len >= 3:
            self.register_dict["r8d"] = AbstractType.ANY_INT
        if para_len >= 4:
            self.register_dict["r9d"] = AbstractType.ANY_INT
        if para_len > 4:
            for i in range(4, para_len):
                self.memory_array[
                    self.register_dict["rsp"] + 8 * (i + 1)
                    ] = AbstractType.ANY_INT
        '''

        def get_value(x: AbstractType | str | Address | ArrayAddress | int) -> AbstractType | None | int:
            if isinstance(x, AbstractType):
                return x
            elif isinstance(x, str):
                if isinstance(self.register_dict[x], AbstractType):
                    return self.register_dict[x]
                else:
                    return self.register_dict[x]
            elif isinstance(x, Address):
                if isinstance(self.memory_array[get_value(x.operand) + x.offset], AbstractType):
                    return self.memory_array[get_value(x.operand) + x.offset]
                else:
                    return self.memory_array[get_value(x.operand) + x.offset]
            elif isinstance(x, ArrayAddress):
                y = get_value(x.operand1)
                z = get_value(x.operand2)
                if isinstance(y, AbstractType):
                    if result2 == AbstractType.POSITIVE_INT:
                        y = 1
                    elif result2 == AbstractType.NEGATIVE_INT:
                        y = -1
                    elif result2 == AbstractType.ZERO:
                        y = 0
                    elif result2 == AbstractType.ANY_INT:
                        y = 0
                if isinstance(z, AbstractType):
                    if result2 == AbstractType.POSITIVE_INT:
                        z = 1
                    elif result2 == AbstractType.NEGATIVE_INT:
                        z = -1
                    elif result2 == AbstractType.ZERO:
                        z = 0
                    elif result2 == AbstractType.ANY_INT:
                        y = 0
                return self.memory_array[y + 4 * z + x.offset]
            elif isinstance(x, int):
                if x > 0:
                    return AbstractType.POSITIVE_INT
                elif x == 0:
                    return AbstractType.ZERO
                elif x < 0:
                    return AbstractType.NEGATIVE_INT

            else:
                raise Exception(x)

        def push(x):
            # push x on the stack
            self.register_dict["rsp"] = self.register_dict["rsp"] - 8
            self.memory_array[self.register_dict["rsp"]] = x

        def pop() -> AbstractType | None | str:
            # pop the stack
            value = self.memory_array[self.register_dict["rsp"]]
            self.register_dict["rsp"] = self.register_dict["rsp"] + 8
            return value

        def assign_value(destination: str | Address, value: AbstractType | None | int | AbstractType) -> None:
            if not isinstance(value, AbstractType | None | int | AbstractType):
                raise Exception(value)

            if isinstance(destination, str):
                self.register_dict[destination] = value
            elif isinstance(destination, Address):
                self.memory_array[
                    get_value(destination.operand) + destination.offset
                    ] = value
            else:
                raise Exception(destination)

        match operation.type:
            case OpType.CDQ:
                pass
            case OpType.PUSH:
                operand = operation.operand_list[0]
            case OpType.POP:
                operand = operation.operand_list[0]
                value = pop()
                assign_value(operand, value)
            case OpType.MOV:
                destination = operation.operand_list[0]
                source = operation.operand_list[1]
                if isinstance(source, ArrayAddress):
                    result1 = get_value(source.operand1)
                    result2 = get_value(source.operand2)
                    x = result1
                    y = result2
                    if isinstance(result1, AbstractType):
                        if result1 == AbstractType.POSITIVE_INT:
                            x = 1
                        elif result1 == AbstractType.NEGATIVE_INT:
                            x = -1
                        elif result1 == AbstractType.ZERO or AbstractType.ANY_INT:
                            x = 0
                    if isinstance(result2, AbstractType):
                        if result2 == AbstractType.POSITIVE_INT:
                            y = 1
                        elif result2 == AbstractType.NEGATIVE_INT:
                            y = -1
                        elif result2 == AbstractType.ZERO:
                            y = 0
                        elif result2 == AbstractType.ANY_INT:
                            y = 0
                    index = x + 4 * y + source.offset
                    low_bound = get_value("rsp")
                    up_bound = get_value("rbp")
                    if index <= low_bound or index >= up_bound:
                        print("out of bounds")
                        return AbstractType.ERROR
                    else:
                        assign_value(destination, get_value(source))
                        if get_value(destination) == AbstractType.ANY_INT:
                            # print("cause the destination",destination,"value=ANY_INT, it should be divide as three types")
                            original_register_dict = self.register_dict.copy()
                            assign_value(destination,AbstractType.POSITIVE_INT)
                            self.test(label_name, operation_index + 1,limit_time)
                            self.register_dict = original_register_dict.copy()
                            assign_value(destination,AbstractType.NEGATIVE_INT,limit_time)
                            self.test(label_name, operation_index + 1)
                            self.register_dict = original_register_dict.copy()
                            assign_value(destination,AbstractType.ZERO)
                            self.test(label_name, operation_index + 1,limit_time)
                            return AbstractType.Finish
                else:
                    assign_value(destination, get_value(source))
                    if get_value(destination) == AbstractType.ANY_INT:
                        # print("cause the Mov",destination, "value=ANY_INT, it should be divide as three types")
                        original_register_dict = self.register_dict.copy()
                        assign_value(destination, AbstractType.POSITIVE_INT)
                        self.test(label_name, operation_index + 1,limit_time)
                        self.register_dict = original_register_dict.copy()
                        assign_value(destination, AbstractType.NEGATIVE_INT)
                        self.test(label_name, operation_index + 1,limit_time)
                        self.register_dict = original_register_dict.copy()
                        assign_value(destination, AbstractType.ZERO)
                        self.test(label_name, operation_index + 1,limit_time)
                        return AbstractType.Finish
            case OpType.ADD:
                operand1 = operation.operand_list[0]
                operand2 = operation.operand_list[1]
                if operand1 == "rsp" and isinstance(operand2, int):
                    self.register_dict["rsp"] = self.register_dict["rsp"] + operand2
                else:
                    result = Sign_abstraction.__add__(Sign_abstraction(get_value(operand1)),
                                                      Sign_abstraction(get_value(operand2)))
                    assign_value(operation.operand_list[0], result.type)
                if get_value(operand1) == AbstractType.ANY_INT:
                    # print("cause the ADD",operand1, "value=ANY_INT, it should be divide as three types")
                    original_register_dict = self.register_dict.copy()
                    assign_value(operand1, AbstractType.POSITIVE_INT)
                    self.test(label_name, operation_index + 1,limit_time)
                    self.register_dict = original_register_dict.copy()
                    assign_value(operand1, AbstractType.NEGATIVE_INT)
                    self.test(label_name, operation_index + 1,limit_time)
                    self.register_dict = original_register_dict.copy()
                    assign_value(operand1, AbstractType.ZERO)
                    self.test(label_name, operation_index + 1,limit_time)
                    return AbstractType.Finish

            case OpType.SUB:
                operand1 = operation.operand_list[0]
                operand2 = operation.operand_list[1]
                if operand1 == "rsp" and isinstance(operand2, int):
                    self.register_dict["rsp"] = self.register_dict["rsp"] - operand2
                else:

                    result = Sign_abstraction.__sub__(Sign_abstraction(get_value(operand1)),
                                                      Sign_abstraction(get_value(operand2)))
                    assign_value(operation.operand_list[0], result.type)
                if get_value(operand1) == AbstractType.ANY_INT:
                    # print("cause the SUB",operand1, "value=ANY_INT, it should be divide as three types")
                    original_register_dict = self.register_dict.copy()
                    assign_value(operand1, AbstractType.POSITIVE_INT)
                    self.test(label_name, operation_index + 1,limit_time)
                    self.register_dict = original_register_dict.copy()
                    assign_value(operand1, AbstractType.NEGATIVE_INT)
                    self.test(label_name, operation_index + 1,limit_time)
                    self.register_dict = original_register_dict.copy()
                    assign_value(operand1, AbstractType.ZERO)
                    self.test(label_name, operation_index + 1,limit_time)
                    return AbstractType.Finish
            case OpType.IDIV:
                operand1 = operation.operand_list[0]
                result = Sign_abstraction.__idiv__(Sign_abstraction(get_value(self.register_dict["eax"])),
                                                   Sign_abstraction(get_value(operand1)))
                assign_value("eax", result.type)
                assign_value("edx", result.type)
                if get_value("eax") == AbstractType.ANY_INT:
                    # print("cause the idiv,eax value=ANY_INT, it should be divide as three types")
                    original_register_dict = self.register_dict.copy()
                    assign_value("eax", AbstractType.POSITIVE_INT)
                    assign_value("edx", AbstractType.POSITIVE_INT)
                    self.test(label_name, operation_index + 1,limit_time)
                    self.register_dict = original_register_dict.copy()
                    assign_value("eax", AbstractType.NEGATIVE_INT)
                    assign_value("edx", AbstractType.NEGATIVE_INT)
                    self.test(label_name, operation_index + 1,limit_time)
                    self.register_dict = original_register_dict.copy()
                    assign_value("eax", AbstractType.ZERO)
                    assign_value("edx", AbstractType.ZERO)
                    self.test(label_name, operation_index + 1,limit_time)
                    return AbstractType.Finish
                elif get_value("eax")==AbstractType.ERROR:
                    return AbstractType.ERROR
            case OpType.IMUL:
                if len(operation.operand_list) == 3:
                    result = Sign_abstraction.__imul__(Sign_abstraction(get_value(operation.operand_list[1])), Sign_abstraction(get_value(
                        operation.operand_list[2])))
                    assign_value(operation.operand_list[0], result.type)
                    if get_value(operation.operand_list[0]) == AbstractType.ANY_INT:
                        # print("cause the imul",operation.operand_list[0], "value=ANY_INT, it should be divide as three types")
                        original_register_dict = self.register_dict.copy()
                        assign_value(operation.operand_list[0],AbstractType.POSITIVE_INT)
                        self.test(label_name, operation_index+1,limit_time)
                        self.register_dict = original_register_dict.copy()
                        assign_value(operation.operand_list[0],AbstractType.NEGATIVE_INT)
                        self.test(label_name, operation_index+1,limit_time)
                        self.register_dict = original_register_dict.copy()
                        assign_value(operation.operand_list[0],AbstractType.ZERO)
                        self.test(label_name, operation_index+1,limit_time)
                        return AbstractType.Finish

            case OpType.SAL:
                pass
            case OpType.LEA:
                operand1 = operation.operand_list[0]
                operand2 = operation.operand_list[1]
                if operand2.operand == "rip":
                    # print(" Assertion failed!")
                    # print(" Exiting!")
                    return AbstractType.Finish
                if not isinstance(operand2, Address):
                    raise Exception
                result = get_value(operand2.operand)
                assign_value(operation.operand_list[0], result)
            case OpType.NOP:
                pass

            case OpType.CALL:
                if operation.operand_list[0] == "userDefinedException":
                    print(" Raise userDefinedException!")
                    print(" Exiting!")
                    return AbstractType.ERROR
                push(operation_index)  # push return address
                operation_index = self.parser.label_dict[operation.operand_list[0]]
                self.test(label_name, operation_index,limit_time)
                return AbstractType.Finish

            case OpType.CMP:
                operand1 = operation.operand_list[0]
                operand2 = operation.operand_list[1]
                x = get_value(operand1)
                y = get_value(operand2)
                # print(operand1,x)
                # print(operand2,y)
                if isinstance(x, int):
                    if isinstance(y, int):
                        if x > y:
                            self.compare = AbstractType.POSITIVE_INT
                        if x == y:
                            self.compare = AbstractType.ZERO
                        if x < y:
                            self.compare = AbstractType.NEGATIVE_INT
                    elif isinstance(y, AbstractType):
                        if y == AbstractType.POSITIVE_INT:
                            if x <= 0:
                                self.compare = AbstractType.POSITIVE_INT
                            if x > 0:
                                self.compare = AbstractType.ANY_INT
                        if y == AbstractType.ZERO:
                            if x == 0:
                                self.compare = AbstractType.ZERO
                            if x > 0:
                                self.compare = AbstractType.POSITIVE_INT
                            if x < 0:
                                self.compare = AbstractType.NEGATIVE_INT
                        if y == AbstractType.ANY_INT:
                            self.compare = AbstractType.ANY_INT
                        if y == AbstractType.NEGATIVE_INT:
                            if x < 0:
                                self.compare = AbstractType.ANY_INT
                            if x >= 0:
                                self.compare = AbstractType.POSITIVE_INT
                elif isinstance(x, AbstractType):
                    if isinstance(y, AbstractType):
                        if y == AbstractType.ANY_INT or x == AbstractType.ANY_INT:
                            self.compare = AbstractType.ANY_INT
                        elif y == AbstractType.ZERO:
                            if x == AbstractType.ZERO:
                                self.compare = AbstractType.ZERO
                            if x == AbstractType.POSITIVE_INT:
                                self.compare = AbstractType.POSITIVE_INT
                            if x == AbstractType.NEGATIVE_INT:
                                self.compare = AbstractType.NEGATIVE_INT
                        elif y == AbstractType.POSITIVE_INT:
                            if x == AbstractType.ZERO or x == AbstractType.NEGATIVE_INT:
                                self.compare = AbstractType.NEGATIVE_INT
                            elif x == AbstractType.POSITIVE_INT:
                                self.compare = AbstractType.ANY_INT
                        elif y == AbstractType.NEGATIVE_INT:
                            if x == AbstractType.ZERO or x == AbstractType.POSITIVE_INT:
                                self.compare = AbstractType.POSITIVE_INT
                    if isinstance(y, int):
                        if x == AbstractType.ANY_INT:
                            self.compare = AbstractType.ANY_INT
                        elif y > 0:
                            if x == AbstractType.ZERO or x == AbstractType.NEGATIVE_INT:
                                self.compare = AbstractType.NEGATIVE_INT
                            if x == AbstractType.POSITIVE_INT:
                                self.compare = AbstractType.ANY_INT
                        elif y == 0:
                            if x == AbstractType.ZERO:
                                self.compare = AbstractType.ZERO
                            if x == AbstractType.POSITIVE_INT:
                                self.compare = AbstractType.POSITIVE_INT
                            if x == AbstractType.NEGATIVE_INT:
                                self.compare = AbstractType.NEGATIVE_INT
                        elif y < 0:
                            if x == AbstractType.ZERO or x == AbstractType.POSITIVE_INT:
                                self.compare = AbstractType.POSITIVE_INT
                            if x == AbstractType.NEGATIVE_INT:
                                self.compare = AbstractType.ANY_INT
                    if self.compare==AbstractType.ANY_INT:
                        # print("cause the compare value=ANY_INT, it should be divide as three types")
                        original_register_dict = self.register_dict.copy()
                        self.compare=AbstractType.POSITIVE_INT
                        self.test(label_name, operation_index+1,limit_time)
                        self.register_dict = original_register_dict.copy()
                        self.compare=AbstractType.NEGATIVE_INT
                        self.test(label_name, operation_index+1,limit_time)
                        self.register_dict = original_register_dict.copy()
                        self.compare=AbstractType.ZERO
                        self.test(label_name, operation_index+1,limit_time)
                        return AbstractType.Finish

                return self.compare
            case OpType.RET:
                result_address: str | None = pop()
                if result_address is None:
                    # print(" Finishing!")
                    # print(f" Result is {get_value('eax')}")
                    return AbstractType.Finish
                elif isinstance(result_address, int):
                    # print(" Returning")
                    # print(f" result is {get_value('eax')}")
                    operation_index = result_address

            case OpType.JGE:
                if self.compare == AbstractType.POSITIVE_INT or self.compare == AbstractType.ZERO:
                    operation_index = self.parser.label_dict[
                        operation.operand_list[0]
                    ]
                    self.test(label_name, operation_index,limit_time)
                    return AbstractType.Finish

            case OpType.JG:
                if self.compare == AbstractType.POSITIVE_INT:
                    operation_index = self.parser.label_dict[
                        operation.operand_list[0]
                    ]
                    self.test(label_name, operation_index,limit_time)
                    return AbstractType.Finish

            case OpType.JS:
                if self.compare == AbstractType.NEGATIVE_INT:
                    operation_index = self.parser.label_dict[
                        operation.operand_list[0]
                    ]
                    self.test(label_name, operation_index,limit_time)
                    return AbstractType.Finish

            case OpType.JMP:
                operation_index = self.parser.label_dict[operation.operand_list[0]]
                self.test(label_name, operation_index,limit_time)
                return AbstractType.Finish

            case OpType.JLE:
                if self.compare != AbstractType.POSITIVE_INT:
                    operation_index = self.parser.label_dict[
                        operation.operand_list[0]
                    ]
                    self.test(label_name, operation_index,limit_time)
                    return AbstractType.Finish

            case OpType.JL:
                if self.compare == AbstractType.NEGATIVE_INT:
                    operation_index = self.parser.label_dict[
                        operation.operand_list[0]
                    ]
                    self.test(label_name, operation_index,limit_time)
                    return AbstractType.Finish

            case OpType.JNS:
                if self.compare == AbstractType.POSITIVE_INT:
                    operation_index = self.parser.label_dict[
                        operation.operand_list[0]
                    ]
                    self.test(label_name, operation_index,limit_time)
                    return AbstractType.Finish

            case OpType.JNE:
                if self.compare != AbstractType.NEGATIVE_INT:
                    operation_index = self.parser.label_dict[
                        operation.operand_list[0]
                    ]
                    self.test(label_name, operation_index,limit_time)
                    return AbstractType.Finish

            case _:
                raise Exception(OpType)

    def test(self, label_name: str, operation_index,limit_time):
        while operation_index < len(self.parser.code_list):
            limit_time=limit_time+1
            code = self.parser.operation_list[operation_index]
            operation = code.operation
            if limit_time>100:
                #  print("Out of loop limit.Program end")
                return 0

            result = self.run(label_name, operation, operation_index,limit_time)
            if result == AbstractType.Finish:
                return 0
            elif result == AbstractType.ERROR:
                print("ERROR")
                return 1
            operation_index = operation_index + 1

        print("result:", self.register_dict["eax"])

    def testfirst(self, label_name: str):
        index = 0
        operation_index = self.parser.label_dict[label_name]
        self.test(label_name, operation_index,index)


if __name__ == "__main__":
    # parser = Parser("TestCode\\foo.c")
    # parser = Parser("TestCode\\div.c")
    # parser = Parser("TestCode\\userDefinedException.c")
    parser = Parser("userDefinedException.c")

    executor = Abstractexecutor(parser)
    start_time = time.time()

    # executor.run("loop", [8])
    # executor.run("loop", [3])
    # executor.run("fib2", [-1])
    # executor.run("loop")
    # executor.run("sum")
    # executor.run("div0", [1])
    # executor.run("div_a_b1", [1, 2])
    # executor.run("div_a_b5", [1, 2])
    # executor.run("array1", [2])
    # executor.run("array2", [2])
    # executor.run("array3", [4])

    # executor.test("div0", 1, 10)
    # executor.test("div_a_b1", 2, 10)
    # executor.test("div_a_b2", 2, 10)
    # executor.test("div_a_b3", 2, 10)
    # executor.test("div_a_b4", 2, 5)
    # executor.test("div_a_b5", 2, 5)
    # executor.test("fib1", 1, 5)
    # executor.test("user1", 3, 16)
    # executor.test("array1", 1, 5)
    # executor.test("array4", 1, 5)
    executor.testfirst("fib3")
    end_time = time.time()
    elapsed_time = end_time - start_time
    print(f"time: {elapsed_time} s")
