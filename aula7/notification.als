/*

 

Finish the specification of this notification concept,

including its events, scenarios, and operational principles.

 

*/

 

sig Event {}

 

sig User {

                var subscriptions : set Event,

                var notifications : set Event

}

 

 

 

 

 

pred stutter {

                subscriptions' = subscriptions

                notifications' = notifications

}

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

pred read [u : User] {

                // Read all notifications

                // all of u's notifications will be erasred

 

                some u.notifications

               

                notifications' = notifications - u->Event

                subscriptions' = subscriptions

}

 

 

 

pred subscribe [u : User, e : Event] {

                // Subscribe to an event

               

                e not in u.subscriptions

 

                subscriptions' = subscriptions + u->e

                notifications' = notifications

}

 

 

 

pred unsubscribe [u : User, e : Event] {

                // Unsubscribe from an event

                // Note: notifications from that event should be erased

               

                e in u.subscriptions

 

                subscriptions' = subscriptions - u->e

                notifications' = notifications - u->e

}

 

 

 

pred occur [e : Event] {

                // Occurrence of an event

                // Users who subscribe to e will be notified of e

               

                (all u :User | u.notifications' = u.notifications + subscriptions.e)

                // notifications' = notifications + subscriptions :> e

                subscriptions' = subscriptions

}

 

 

 

fact {

                // Init

                no subscriptions

                no notifications

 

                // Dynamics

                always {

                                stutter

                                or

                                (some u : User | read[u])

                                or

                                (some u : User, e : Event | subscribe[u,e])

                                 or

                                (some u : User, e : Event | unsubscribe[u,e])

                                or

                                (some e : Event | occur[e])

                }

}

 

 

 

 

 

 

 

 

 

 

// Validation

 

run Example {}

 

run Scenario1 {

                // An event is subscribed, then occurs, and the respective notification is read

                some u : User, e : Event {

                                subscribe[u,e]; occur[e]; read[u]

                }

} expect 1

 

 

 

run Scenario2 {

                // An event is subscribed, unsubscribed, and then occurs

                some u : User, e : Event {

                                subscribe[u,e]; unsubscribe[u,e]; occur[e]

                }

} expect 1

 

 

 

run Scenario3 {

                // An event is subscribed by two users and then occurs

                some disj u1,u2 : User, e : Event {

                                subscribe[u1,e]; subscribe[u2,e]; occur[e]

                }

} expect 1

 

 

 

run Scenario4 {

                // An user subscribes two events, then both occur, then unsubscribes one of them, and finally reads the notifications

                some u : User, disj e1,e2 : Event {

                                subscribe[u,e1]; subscribe[u,e2]; occur[e1]; occur[e2]; unsubscribe[u,e1]; read[u]

                }

} expect 1

 

 

 

run Scenario5 {

                // An user subscribes the same event twice in a row

                some u : User, e : Event {

                                subscribe[u,e]; subscribe[u,e]

                }

} expect 0

 

 

 

run Scenario6 {

                // Eventually an user reads nofications twice in a row

                eventually some u : User {

                                read[u]; read[u]

                }

} expect 0

// Verification 

check OP1 {
	// Users can only have notifications of subscribed events

}

check OP2 {
	// Its not possible to read notifications before some event is subscribed

}

check OP3 {
	// Unsubscribe undos subscribe

}

check OP4 {
	// Notify is idempotent

}

check OP5 {
	// After reading the notifications it is only possible to read again after some notification on a subscribed event occurs

}
