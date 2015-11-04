//SIGNATURES

sig Address {}
sig DateTime {}
sig Amount {}
sig Email {}
sig PhoneNum {}

sig RegisteredUser {
	email: one Email,
	phone: one PhoneNum,
	actions: set Action
}

abstract sig Action {
	start: one Address,
	destination: one Address
}

sig Request extends Action {
	proposal: one RequestProposal
}

sig Reserve extends Action {
	datetime: one DateTime,
	proposal: one ReservationProposal
}

abstract sig Proposal {
	fare: one Amount,
	taxi: lone Taxi
}

sig RequestProposal extends Proposal {}

sig ReservationProposal extends Proposal {}

sig City {
	zones: set Zone
} {
	one City
	#zones >= 1
}

sig Zone {
	queue: one Queue
}

sig Taxi {}

sig Queue {
	waiting: set Taxi
}

//FACTS

//user constraints
fact UserProperties {
	//no two registered users can have the same email
	all disj u1,u2: RegisteredUser | (u1.email != u2.email)

	//no two registered users can have the same phone number
	all disj u1,u2: RegisteredUser | (u1.phone != u2.phone)
}

//taxi can not wait in more than one queue
fact TaxiQueueing {
	all t: Taxi | lone q: Queue | t in q.waiting
}


fact ZoneProperties {
	//every queue has to be asociated with exactly one zone
	all q: Queue | (one z: Zone | z.queue = q)

	//each zone has to be part of the city
	one c: City | c.zones = Zone
}

fact TaxiAndProposal {
	//if a taxi accepts proposal it is not in the queue
	all r: Proposal, q: Queue | no (r.taxi & q.waiting)
	
	//taxi can't accept more than one proposal at the time
	all t: Taxi | lone r: Proposal | t in r.taxi

	//differen proposal should be generated for each request/reservation
	all p: RequestProposal | one r: Request | p in r.proposal
	all p: ReservationProposal | one r: Reserve | p in r.proposal

	//amount should only exist if associated within proposal
	all a: Amount | some p: Proposal | p.fare = a
	
}


fact ActionPropreties {
	//every action should be done by the user
	all a: Action | one u: RegisteredUser | a in u.actions

	//starting point and destination must be different
	all a: Action | a.start != a.destination

	//datetime must always be associated with reservation
	all d: DateTime | one r: Reserve | d in r.datetime

	//user can not reserve multiple taxies at the same time
	all disj r1,r2: Reserve | (r1.datetime = r2.datetime) implies no u: RegisteredUser | (r1 in u.actions) and (r2 in u.actions)
}


// ASSERTIONS



pred show {}

run show for 4 but 3 Reserve
