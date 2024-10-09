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


// Note in the above there are two relations called "projects".
// The desambiguation syntax is
// Person <: projects     /     Course <: projects
// In particular for a project pr we will write
// (Person <: projects).pr  and  (Course <: projects).pr
// for the sets of Persons and Courses associated with it




// Specify the following properties.
// You can check their correctness with the different commands and
// when specifying each property you can assume all the previous ones to be true.



pred inv1 {
	// Only students can be enrolled in courses

	all p : Person | (some p.enrolled) implies p in Student

}



pred inv2 {
	// Only professors can teach courses
	// more succinct alternative to the previous
	
        teaches in Professor -> Course
}



pred inv3 {
	// Courses must have teachers

	// all c : Course | some teaches.c

	// a more succinct way to state this:
	// apply a multiplicity modifier to the relation
	
	teaches in Person some -> Course
}



pred inv4 {
	// Projects are proposed by one course

	all p : Project | one (Course <: projects).p
}



pred inv5 {
	// Only students work on projects
	
	all p : Person | (some pr : Project | p->pr in projects) implies p in Student 

	// ALTERNATIVELY (and more compact) :

	all pr : Project | (Person <: projects).pr in Student


	// and projects must have someone working on them

	all pr : Project | some (Person <: projects).pr
}



pred inv6 {
	// Students only work on projects of courses they are enrolled in

	// all s : Student, c : Course |
	//     (some s.projects & c.projects) implies s->c in enrolled


	// ALTERNATIVELY, with universal quantifs only:

        // all s : Student, c : Course, pr : Project | 
	//       c->pr in projects and s->pr in projects implies s->c in enrolled


	// OR:

        // all s : Student, pr : s.projects | 
	//       (Course <: projects).pr in s.enrolled


	// ALTERNATIVELY, chaining relations:

        all s : Student | s.projects in s.enrolled.projects
			 
}



pred inv7 {
	// Students work on at most one project per course
	// the "lone" quantifier and cardinality operator come in handy:

        // all s : Student, c : Course | lone pr : Project | pr in (c.projects & s.projects)

        all s : Student, c : Course | lone (c.projects & s.projects)
}



pred inv8 {
	// A professor cannot teach herself

	all p : Professor | no (p.teaches & p.enrolled)

	// OR, symmetrically, 

	// all c : Course | no (teaches.c & enrolled.c)
	
}



pred inv9 { 
	// A professor cannot teach colleagues

	// all p1, p2 : Professor | 
	//   (some ... )
	//    implies
	//   (no ... )

	// Or using chaining:
	     
	//  all p1 : Professor | no p2 : Professor | p2 in teaches.(p1.teaches) and p2 in enrolled.(p1.teaches)

       all p : Professor | no teaches.(p.teaches) & enrolled.(p.teaches)

}



pred inv10 {
	// Only students have grades
	// Note that grades is a TERNARY relation! 

	// all c : Course | all g : Grade | all p : Person | 
	//  c->p->g in grades implies p in Student

	// all c : Course | all g : Grade | c.grades.g in Student

	Course.grades.Grade in Student

}



pred inv11 {
	// Students only have grades in courses they are enrolled

	// all c : Course | all g : Grade | c.grades.g in enrolled.c

	all c : Course | c.grades.Grade in enrolled.c

	// WRONG! This means
	// "students that have a grade in some course are enrolled in some course"
	Course.grades.Grade in enrolled.Course
}



pred inv12 {
	// Students have at most one grade per course
	
	// all s : Student, c : Course |
	//   lone g : Grade | c->s->g in grades

	all s : Student, c : Course | lone s.(c.grades)



	// WRONG! This means
	// "There is at most one grade for the entire set of students and courses"
	// lone Student.(Course.grades)

}



pred inv13 {
	// A student with the highest mark in a course must have worked on a project on that course

	// all c : Course, p : Person | last in p.(c.grades) implies
	//   some pr :Project | p->pr in projects and c->pr in projects

	all c : Course, p : Person | last in p.(c.grades) implies some p.projects & c.projects

}



pred inv14 {
	// A student cannot work with the same student in different projects

	// In other words, two students can work together in AT MOST ONE project...

        all disj s1, s2 : Student | lone s1.projects & s2.projects

}



pred inv15 {
	// Students working on the same project in a course cannot have marks differing by more than one unit

	all c : Course, disj x,y : Student, g1 : x.(c.grades), g2 : y.(c.grades) |
	  (some c.projects & x.projects & y.projects) implies g1 in g2.(prev+iden+next)
}
