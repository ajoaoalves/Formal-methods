from z3 import *

aulas = [1, 2, 3, 4, 5]
formadores = ['Ana', 'Beatriz', 'Carlos']

x = {}
for f in formadores:
    x[f] = {}
    for a in aulas:
        x[f][a] = Bool("%s,%d" % (f, a))

s = Solver()

# O Carlos não pode dar a primeira aula.
s.add(Not(x['Carlos'][1]))

# Se a Beatriz der a primeira aula, não poderá dar a última.
s.add(Implies(x['Beatriz'][1], Not(x['Beatriz'][5])))

# Cada aula tem pelo menos um formador.
for a in aulas:
    s.add(Or([x[f][a] for f in formadores]))

# As quatro primeiras aulas têm no máximo um formador.
for a in aulas:
    if a != 5:
        for f1 in formadores:
            for f2 in formadores:
                if f1 < f2:
                    s.add(Or(Not(x[f1][a]), Not(x[f2][a])))

# A última aula pode ter no máximo dois formadores.
for f1 in formadores:
    for f2 in formadores:
        for f3 in formadores:
            if f1 != f2 and f1 != f3 and f2 != f3:
                s.add(Implies(And(x[f1][5], x[f2][5]), Not(x[f3][5])))

# Nenhum formador pode dar 4 aulas consecutivas.
for f in formadores:
    for a in aulas:
        if a <= 2:
            s.add(Implies(x[f][a], And(Not(x[f][a+1]), Not(x[f][a+2]), Not(x[f][a+3]))))

def aux(m):
    p = []
    for f in formadores:
        for a in aulas:
            if is_true(m[x[f][a]]):
                p.append(x[f][a])
            else:
                p.append(Not(x[f][a]))
    return Not(And(p))

s.push()
i = 0
while s.check() == sat:
    i += 1
    m = s.model()
    print("\nSolução %d:" % i)
    for f in formadores:
        for a in aulas:
            if is_true(m[x[f][a]]):
                print("%s dá a aula %s" % (f, a))
    s.add(aux(m))

print("\nTotal de alocações possíveis:", i)
s.pop()
