

sig Resource {}

sig User {
	var reservations : set Resource
}

var sig Available in Resource {}


// Clauses in a predicate are interpreted as conjuncts
// -- no need for "and".
// The use of prime notation ( ' ) allows for system
// actions to be specified.
// Clauses referring only to the pre-state can be seen
// as pre-conditions


pred reserve[u : User, r : Resource] {
	// Make a reservation

	// Precondition: a logic condition on the pre-state
	
	r in Available

	// Effect: a formula involving pre- and post-state
	
	Available' = Available - r
	reservations' = reservations + u->r
}



pred cancel[u : User, r : Resource] {
	// Cancel a reservation

	r in u.reservations
	
	Available' = Available + r
	reservations' = reservations - u->r	
}



pred use[u : User, r : Resource] {
	// Use a reserved resource - does not liberate it 

	r in u.reservations
	
	Available' = Available
	reservations' = reservations - u->r	
}



pred cleanup {
	// Make all used resources available again

	some Resource - Available - User.reservations

	Available' = Resource - User.reservations
	reservations' = reservations
}



pred stutter {
	Available' = Available
	reservations' = reservations
}


fact {
	// System Init
	Available = Resource
	no reservations

	// Dynamics
	always {
		(some u : User , r : Resource | reserve[u,r])
	 	or 
	 	(some u : User , r : Resource | cancel[u,r])
		or 
		(some u : User , r : Resource | use[u,r])
		or 
		cleanup
		or 
		stutter
	}
}

// Validation

run Example {
	// Empty run to be used for simulation
}

run Scenario1 {
	// An user reserves a resource, uses it, and finally a cleanup occurs
	some u:User,r:Resource {
		reserve[u,r];use[u,r];cleanup
	}

} expect 1

run Scenario2 {
	// An user reserves a resource, cancels the reservation, and reserves again
	some u:User,r:Resource {
		reserve[u,r];cancel[u,r];reserve[u,r]
	}

} expect 1

run Scenario3 {
	// An user reserves two resources, cancels one, uses the other, and finally a cleanup occurs
	some u:User,r1:Resource,r2:Resource {
		reserve[u,r1];reserve[u,r2];cancel[u,r1];use[u,r2];cleanup
	}

} expect 1

run Scenario4 {
	// Two users try to reserve the same resource
	some u1:User,u2:User,r:Resource {
		reserve[u1,r];reserve[u2,r]
	}

} expect 0

run Scenario5 {
	// Eventually a cleanup is performed twice in a row
  eventually (cleanup;cleanup)

} expect 0

// Verification

check OP1 {
	// Reserved resources aren't available

	all r : Resource, u:User | always (u->r in reservations implies r not in Available)
}

check OP1b {
	// Reserved are reserved by at most one user

	always (all r:Resource | lone reservations.r)
}

check OP2 {
	// Used resources were reserved before

	all u : User, r : Resource | always (use[u,r] implies once r in u.reservations)
	

}

check OP3 {
	// Used resources can only be reserved again after a cleanup
		all u1,u2 : User, r : Resource | always ( reserve[u1,r] or reserve[u2,r] implies ( cleanup releases not (reserve[u2,r] and use[u1,r])))
}

check OP4 {
	// After a cleanup all unreserved resources are available
	always (cleanup implies after  
		all r:Resource | r in Available iff all u:User | r not in u.reservations)

}

check OP5 {
	// Cancel undoes reserve
  
  all u:User, r : Resource |
  	always ((reserve[u,r];cancel[u,r])
      implies 
      Available'' = Available and reservations'' = reservations)

}

check OP6 {
	// If a cleanup occurs some resource was used before
	//always( cleanup implies (some u:User, r:Resource | once reserve[u,r]))

	always(cleanup implies once (some u : User, r:Resource | use[u,r]))

}

check OP7 {
	// Used resources were not canceled since being reserved
	//all u: User, r: Resource | always (use[u, r] implies (r in reservations[u]))
	//all u: User, r: Resource |	always (use[u, r] implies once reserve[u,r])
	all u: User, r: Resource |	always (use[u, r] implies (not cancel[u,r] since reserve[u,r]))

}

check OP8 {
	// Reserved resources can be used while not used or canceled
	//all u1:User, u2: User, r: Resource | always (use[u1, r] implies (not (use[u2,r] and cancel[u2,r])))
	all u:User,r:Resource | always (reserve[u,r] implies after ((use[u,r] or cancel[u,r]) releases r in u.reservations))

}

check OP9 {
  // The first event to occur will be a reservation
  always stutter or (stutter until (some u:User,r:Resource | reserve[u,r]))


}


check OP10 {
    // Se não ocorrerem limpezas nem cancelamentos, os recursos disponíveis diminuem
	always(not cleanup and all u : User,r:Resource | not cancel[u,r]) implies always (Available' in Available)
	
}
