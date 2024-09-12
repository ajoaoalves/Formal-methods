from z3 import * 

#BASE PARA ESTUDAR UM FEATURE MODEL

Survey,License,ABTesting,Statistics,QA,AdvancedLicense,BasicLicense,BasicQA,MultimediaQA = Bools("Survey License ABTesting Statistics QA AdvancedLicense BasicLicense BasicQA MultimediaQA")
features = [Survey,License,ABTesting,Statistics,QA,AdvancedLicense,BasicLicense,BasicQA,MultimediaQA]

s = Solver()

# Survey is a root reature
s.add(Survey)

# License is a mandatory sub-feature of Phone

s.add(License == Survey)

# AB Testing is a mandatory sub-feature of Phone

s.add(ABTesting == Survey)

# Statistics is an optional sub-feature of Phone

s.add(Implies(Statistics,Survey))

# QA is a mandatory sub-feature of Phone

s.add(QA == Survey)

# Advanced license and basic license are xor sub-features of License
s.add(Or(AdvancedLicense,BasicLicense) == License)
s.add(Not(And(AdvancedLicense,BasicLicense)))

# BasicQA and MultimediaQA are or sub-features of Media
s.add(Or(BasicQA,MultimediaQA) == QA)

# ABTesting excludes Basic License
s.add(Not(And(ABTesting,BasicLicense)))

# ABTesting requires Statistics
s.add(Implies(ABTesting,Statistics))

# MultimediaQA excludes Basic License
s.add(Not(And(BasicLicense,MultimediaQA)))

if s.check() == sat:
  print("Feature model is non void")
else:
  print("Feature model is void")

 #RESPOSTA: Feature model is non void (Há pelo menos uma configuração de caracteristicas que satisfaz todas as restrições do modelo)

#PARA VERIFICAR SE ALGUMA FEATURE ÉSTA MORTA 

for f in features:
  s.push()
  s.add(f)
  if s.check() == unsat:
    print("Feature " + f.decl().name() + " is dead!")
  s.pop()

#RESPOSTA: Feature BasicLicense is dead!

#PARA VERIFICAR SE ALGUMA FEATURE É CORE(É ESSENCIAL)

for f in features:
  s.push()
  s.add(Not(f))
  if s.check() == unsat:
    print("Feature " + f.decl().name() + " is core!")
  s.pop()

#RESPOSTA: 
# Feature Survey is core!
# Feature License is core!
# Feature ABTesting is core!
# Feature Statistics is core!
# Feature QA is core!
# Feature AdvancedLicense is core!

#PARA ENUMERAR TODOS OS POSSIVEIS PRODUTOS OU CONTAR

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

#RESPOSTA:
# Survey License ABTesting Statistics QA AdvancedLicense BasicQA 
# Survey License ABTesting Statistics QA AdvancedLicense MultimediaQA 
# Survey License ABTesting Statistics QA AdvancedLicense BasicQA MultimediaQA 
# There are 3 possible products!

#To the questions - If AB testing was mandatory what would be the core features? Survey, License, ABTesting, Statistics, QA, AdvancedLicense