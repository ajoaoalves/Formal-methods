open util/ordering[Grade]

sig Person {
	teaches : set Course,
	enrolled : set Course,
	projects : set Project //OVERLOADING projects
}

sig Professor,Student in Person {}  //extends subtipos disjuntos e in não obriga a serem disjuntos ou sejam podem ser professores e alunos

sig Course {
	projects : set Project, //OVERLOADING projects ------> Quando quero falar deste project faço Course <: projects
	grades : Person -> Grade //relação ternária ->no curso c o aluno p tem nota n
}

sig Project {}

sig Grade {}
// Specify the following properties.
// You can check their correctness with the different commands and
// when specifying each property you can assume all the previous ones to be true.

pred inv1 {
	// Only students can be enrolled in courses

    all p : Person | (some p.enrolled) implies p in Student
	
}


pred inv2 {
	// Only professors can teach courses
	// more succint alternative to the previous

	teaches in Professor -> Course

}


pred inv3 {
	// Courses must have teachers 

	all c : Course | some teaches.c

	//a more succint way to state this:
	//apply a multiplicity modifier to the relation

	teaches in Person some -> Course

}


pred inv4 {
	// Projects are proposed by one course

    all p : Project | one (Course <: projects).p

}


pred inv5 {
	// Only students work on projects and 

    all p: Person | (some pr  : Project | p->pr in projects) implies p in Student

    //ALTERNATIVELY (and more compact): 

    all pr : Project | (Person <: projects).pr in Student


	// projects must have someone working on them

    all pr : Project | some (Person <: projects).pr

}


pred inv6 {
	// Students only work on projects of courses they are enrolled in 

    //all x : Student, c : Course | (some s.projects & c.projects) implies s->c in enrolled

    //ALTERNATIVELY with universal quantifs only:

    //all s : Student, c : Course, pr: Project | c->pr in projects and s->pr in projects implies s->c in enrolled

    //OR:

    // all s: Student, pr : s.projects | (Course <: projects).pr in s.enrolled

    //ALTERNATIVE, chaining relations:

    all s : Student | s.projects in s.enrolled.projects


}


pred inv7 {
	// Students work on at most one project per course

}


pred inv8 {
	// A professor cannot teach herself

}


pred inv9 {
	// A professor cannot teach colleagues

}


pred inv10 {
	// Only students have grades
    //Note that grades its a TERNARY relation!

    //all c: Course | all g:Grade | all p:Person | c->p->g in grades implies p in Student

    //all c : COurse | all g : Grade | ... in Student ... in Student

}


pred inv11 {
	// Students only have grades in courses they are enrolled

    //all c : Course | all g:Grade | ... in enrolled.c 

    all c : Course | ... in enrolled.c

}


pred inv12 {
	// Students have at most one grade per course

    //all s : Student, c : Course | 

}


pred inv13 {
	// A student with the highest mark in a course must have worked on a project on that course


}


pred inv14 {
	// A student cannot work with the same student in different projects

}


pred inv15 {
	// Students working on the same project in a course cannot have marks differing by more than one unit

}
