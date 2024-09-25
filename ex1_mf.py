from z3 import *

EShop,Catalogue,Payment,Security,GUI,Banners,Offers,Search,BankDraft,CreditCard,High,Medium,PC,Mobile,Info,Basic,Advanced,Visa,AmericanExpress,Image,Price,Description = Bools("EShop Catalogue Payment Security GUI Banners Offers Search BankDraft CreditCard High Medium PC Mobile Info Basic Advanced Visa AmericanExpress Image Price Description")
features = [EShop,Catalogue,Payment,Security,GUI,Banners,Offers,Search,BankDraft,CreditCard,High,Medium,PC,Mobile,Info,Basic,Advanced,Visa,AmericanExpress,Image,Price,Description ]

s = Solver()

# EShop is a root reature
s.add(EShop)

# Catalogue is a mandatory sub-feature of EShop
s.add(Catalogue == EShop)

# Payment is a mandatory sub-feature of EShop
s.add(Payment == EShop)

# Security is an optional sub-feature of EShop
s.add(Security==EShop)

# GUI is a mandatory sub-feature of EShop
s.add(GUI == EShop)

# Banners is an optional sub-feature of EShop
s.add(Implies(Banners,EShop))

#RAMO ABAIXO CATALOGUE

# Offers is an optional sub-feature of Catalogue
s.add(Implies(Offers,Catalogue))

# Info is a mandatory sub-feature of Catalogue
s.add(Info == Catalogue)

# Search is an optional sub-feature of Catalogue
s.add(Implies(Search,Catalogue))

# Image,Description and Price are or sub-features of Info
s.add(Or(Image,Description,Price) == Info)

# Basic and Advanced are or sub-features of Search
s.add(Or(Basic,Advanced) == Search)

#RAMO ABAIXO DO PAYMENT

# Basic and Advanced are or sub-features of Payment
s.add(Or(BankDraft,CreditCard) == Payment)

# Basic and Advanced are or sub-features of Payment
s.add(Or(Visa,AmericanExpress) == CreditCard)

#RAMO ABAIXO DO SECURY

#High e Medium are xor sub-features of Security
s.add(Or(High,Medium) == Security)
s.add(Not(And(High,Medium)))

#RAMO ABAIXO DO GUI

# Basic and Advanced are or sub-features of Payment
s.add(Or(PC,Mobile) == GUI)

# Banners excludes Mobile
s.add(Not(And(Banners,Mobile)))

# Credit Card requires Hight
s.add(Implies(CreditCard,High))

s.push()
i = 0
while s.check() == sat:
  i += 1
  m = s.model()
  p = []
  for f in features:
    if is_true(m[f]):
      p.append(f)
      print(f.decl().name(),end=" ")
    else:
      p.append(Not(f))
  print()
  s.add(Not(And(p)))
print("There are " + str(i) + " possible products!")
s.pop()