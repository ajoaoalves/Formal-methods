from z3 import *

pessoas = ["Ana","Nuno","Pedro","Maria"]
gabs = [1,2,3]
x = {}
for p in pessoas:
    x[p] = {}
    for g in gabs:
        x[p][g] = Bool("%s,%d" % (p,g))

s = Solver()
 
# Cada pessoa ocupa pelo menos um gabinete. Isto fica(x(a,1) ou x(a,2) ou x(a,3)), onde a é de Ana e os numeros são os numeros dos gabinetes. Fazemos o resto para o resto das pessoas 

for p in pessoas:
  s.add(Or([x[p][g] for g in gabs]))

# Cada pessoa ocupa no máximo um gabinete.

for p in pessoas:
   s.add(Implies(x[p][1], And(Not(x[p][2]), Not(x[p][3]))))
   s.add(Implies(x[p][2], Not(x[p][3])))

# O Nuno e o Pedro não podem partilhar gabinete.

for g in gabs:
  s.add(Not(And(x["Nuno"][g], x["Pedro"][g])))

for g in gabs:
  s.add(Implies(x["Pedro"][g],Not(x["Nuno"][g])))

# Se a Ana ficar sozinha num gabinete, então o Pedro também terá
# que ficar sozinho num gabinete.

#VERSÃO PROF FRADE

#anaSo = Or([And(x["Ana"][g],
#                Not(x["Nuno"][g]),
#                Not(x["Pedro"][g]),
#                Not(x["Maria"][g])) for g in gabs])
#
#pedroSo = And([Implies(x["Pedro"][g],
#                And(Not(x["Nuno"][g]),
#                Not(x["Ana"][g]),
#                Not(x["Maria"][g]))) for g in gabs])
#
#s.add(Implies(anaSo, pedroSo))

#VERSÃO PROF JSP

anaSo = Or([And(x["Ana"][g], Not(x["Nuno"][g]), Not(x["Pedro"][g]), Not(x["Maria"][g])) 
    for g in gabs])

pedroSo1 = Implies(x["Pedro"][1], And(Not(x["Nuno"][1]), Not(x["Ana"][1]), Not(x["Maria"][1])))
pedroSo2 = Implies(x["Pedro"][2], And(Not(x["Nuno"][2]), Not(x["Ana"][2]), Not(x["Maria"][2])))
pedroSo3 = Implies(x["Pedro"][3], And(Not(x["Nuno"][3]), Not(x["Ana"][3]), Not(x["Maria"][3])))
pedroSoo = And(pedroSo1, pedroSo2, pedroSo3)
s.add(Implies(anaSo, pedroSoo))

# Cada gabinete só pode acomodar, no máximo, 2 pessoas.

for g in gabs:
    s.add(And([Implies(And(x[p1][g], x[p2][g]), And(Not(x[p3][g]), Not(x[p4][g])))
        for p1 in pessoas for p2 in pessoas for p3 in pessoas for p4 in pessoas 
            if p1 != p2 and p1 != p3 and p1 != p4 and p2 != p3 and p2 != p4 and p3 != p4]))
    
# A função aux cria uma cláusula de exclusão para evitar que a mesma solução seja encontrada repetidamente.

def aux(m):
    l = []
    for p in pessoas:
        for g in gabs:
            if is_true(m[x[p][g]]):
                l.append(x[p][g])
            else:
                l.append(Not(x[p][g]))
    return Not(And(l))

# Loop principal: Gerar múltiplas soluções

s.push() # Armazena o estado atual do solucionador antes de começar o loop.
i = 0
while s.check() == sat: #  Este loop encontra e imprime todas as soluções possíveis enquanto elas existirem.
    i += 1
    m = s.model()
    print("\nSolução %d:" % i)
    for p in pessoas:
        for g in gabs:
            if is_true(m[x[p][g]]):
                print("%s fica no gabinete %s" % (p,g))
    s.add(aux(m))
s.pop() # Restaura o estado original do solucionador após terminar de encontrar todas as soluções.

#Use agora o SAT solver para testar a veracidade se cada uma das seguintes afirmações:

s.push()
#Se a Maria ocupar o gabinete um, então ela ficará sozinha nesse gabinete.
s.add(Implies(x['Maria'][1], And(Not(x['Ana'][1]), Not(x['Nuno'][1]), Not(x['Pedro'][1]))))
if s.check() == sat:
    print("\nA afirmação é falsa")
else:
    print("\nA afirmação é verdadeira")
s.pop()

s.push()
for g1 in gabs:
    for g2 in gabs:
        if g1 != g2:
            # se Ana e Nuno estiverem no mesmo gabinete g1, então Maria e Pedro devem estar em um gabinete diferente (g2).
            s.add(Implies(And(x['Ana'][g1], x['Nuno'][g1]), And(x['Maria'][g2], x['Pedro'][g2])))
if s.check() == sat:
    print("\nA afirmação é falsa")
else:
    print("\nA afirmação é verdadeira")
s.pop()