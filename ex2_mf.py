sig Feature {
	children : set Feature,
	excludes : set Feature
}
sig Or  extends Feature {}
sig Xor extends Feature {}
one sig Root in Feature {}
sig Optional in Feature {}

pred Invs {
  
      // Shape
  
      // A raiz não pode ter pai
  	
  	  	no f : Feature | Root in f.children
  
      // Todas as features exceto a raiz têm exatamente um pai
  
  		all f : Feature - Root | one p : Feature | f in p.children  
  
      // Todas as features são descendentes da raiz
    
    	all f: Feature | f not in f.^children

 
      // Or e Xor precisam de pelo menos dois filhos
  
  		all o : Or | #o.children >= 2 
  
    	all x : Xor| #x.children >= 2 
 
 
      // Optional 
  
      // A raiz não pode ser opcional
  
  		Root not in Optional

      // Or e Xor não podem ter filhos opcionais
  
  		all o : Or, f : Feature | f in o.children implies f not in Optional
  
    	all x : Xor, f : Feature | f in x.children implies f not in Optional

 
      // Excludes  
  
      // Uma feature não se pode excluir a si própria
  
  		all f : Feature | f->f not in excludes
    
	// Nenhuma feature pode excluir seus descendentes
		all f, d : Feature | d in f.^children implies d not in f.excludes

	// Nenhuma feature pode excluir seus ascendentes
		all f, a : Feature | a in f.^children implies f not in a.excludes
      // A exclusão é mútua
  
  		all x,y : Feature | x->y in excludes implies y->x in excludes
  
      // Os filhos de um Xor não se podem excluir mutuamente
  
  		all x : Xor, f1, f2 : Feature | f1 in x.children and f2 in x.children implies f1 not in f2.excludes and f2 not in f1.excludes
  
}