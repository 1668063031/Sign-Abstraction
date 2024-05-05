class Label:
    def __init__(self, owner, readers):
        self.owner = owner
        read = [readers]
        self.readers = set(read)
        print(
            f">>Logic<<New information flow create | o: {self.owner}"
                    f" --> r: {self.readers}"
        )
        
    def add_reader(self, owner, readers):
        if owner == self.owner:
            if readers=="T":
                self.readers="T"
                print(
                    f">>Logic<< Declassified from owner {owner} by adding reader {readers} || o: {self.owner}"
                    f" --> r: {self.readers}")
                return True
            if readers not in self.readers:
                self.readers.add(readers)
                print(
                    f">>Logic<< Declassified from owner {owner} by adding reader {readers} || o: {self.owner}"
                    f" --> r: {self.readers}")
            else: print(f">>Label<< Reader {readers} already existed inside L : {owner,readers}")
            return True
        else:
            raise Exception("Only the Owners can add new readers")

    def remove_reader(self, owner, removed):
        if owner == self.owner:
            self.readers.discard(removed)
            print(f">>Label<< remove reader, o: {self.owner}, r {self.readers}")
        else:
            raise Exception("Only the owners can remove reader")

    def relabelling(self,owner):
        self.owner = owner
        read = [owner]
        self.readers = set(read)
        print(f">>Label<< Reset label, o: {self.owner}, r {self.readers}")

    def ownerchange(self,owner1,owner2):
        if owner1==self.owner:
            self.owner=owner2
            print(f">>Label<< change owner from {owner1} to {owner2}, o: {self.owner}, r {self.readers}")
        else:
            raise Exception("Only the Owners can add new readers")
            
class Database:
    def __init__(self):
        self.id = []
        self.maxbids = []
        self.number = 0
        self.name = "database"

    def register(self, id, maxbids):
        if id < 0 or maxbids < 0:
            print("illegal number")
            return False
        self.id.append(id)
        self.maxbids.append(maxbids)
        self.number += 1
        return True

    def check_id(self, id):
        return self.maxbids[id] if 0 <= id < len(self.id) else None

    def get_id(self, id):  
        return self.id[id] if 0 <= id < len(self.id) else None   


class auction_House:

    def __init__(self,name):
        self.currentprice = 500
        self.number = 0
        self.currentid = -1
        self.database = Database()
        self.maxid = 0
        self.name=name

    def updateprice(self,id,price,Label):
        if price<self.currentprice:
            print("illegal price")
            return False
        self.currentid = id
        self.currentprice = price
        Label.add_reader(self.name, "T")
    def registmax(self,Customer,price,Label):
        Label.relabelling(Customer.name)
        Label.add_reader(Customer.name, self.name)
        self.database.register(Customer.id,price)
        self.maxid=self.maxid+1
        Label.ownerchange(Customer.name,self.name)
        Label.remove_reader(self.name,Customer.name)
        Label.add_reader(self.name,self.database.name)
    def allocatenumber(self,Label,Customer):
        self.number += 1
        Label.relabelling(self.name)
        Label.add_reader(self.name,"T")
        Label.ownerchange(self.name,Customer.name)
        return self.number

    def checkmax(self,Label):
        Label.add_reader(self.name,self.database.name)
        for m in range (self.maxid):

            maxprice=self.database.check_id(m)
            if maxprice > self.currentprice :
                if self.database.get_id(m)!=self.currentid:
                  print(self.database.get_id(m),self.currentprice+1)
                  self.updateprice(self.database.get_id(m),self.currentprice+1,Label)
                  return 1

class Customer:
    def __init__(self, name):
        self.name = name
        self.current = None
        self.currentid = None
        self.id=-1

    def receive(self,id,price):
        self.currentid = id
        self.current = price

    def allocate(self,auction_House,Label):
        print("Sent number request to auction house" )
        Label.add_reader(self.name,auction_House.name)
        self.id=auction_House.allocatenumber(Label,self)

    def callprice(self,auction_House,Label):
        Label.relabelling(self.name)
        Label.add_reader(self.name,auction_House.name)
       
       
A=auction_House("A")
B=Customer("Bob")
Label1=Label(B.name,B.name)
B.allocate(A,Label1)
C=Customer("Carol")
Label2=Label(C.name,C.name)
C.allocate(A,Label2)
D=Customer("Dave")
Label3=Label(D.name,D.name)
D.allocate(A,Label3)
Label4=Label(A.name,A.name)
Label4.add_reader(A.name,"T")
print(A.currentprice)
A.registmax(C,1000,Label2)
print("start")
B.callprice(A,Label1)
A.updateprice(B.id,700,Label4)
print(A.currentprice)
print(A.currentid,A.currentprice)

Label5=Label(A.name,A.name)
A.checkmax(Label5)

