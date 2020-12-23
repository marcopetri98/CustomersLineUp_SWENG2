open util/ordering[QueueTicket]
open util/time

abstract sig Person {}
abstract sig Ticket {
	ticketOwner: one Customer,
}

// general entities
sig DateTime {}

// entities which extend Person
sig StoreManager extends Person {}
sig Customer extends Person {}
sig CheckpointController extends Person {
	//tickets admitted into the store
	controllerCheckIns: dynamicSet[Ticket],
	//tickets scanned at the exit
	controllerCheckOuts: dynamicSet[Ticket],
}

// entities extending ticket
sig BookingTicket extends Ticket {}
sig QueueTicket extends Ticket {}

// store's signature
sig Store {
	storeManagers: some StoreManager,
	storeControllers: some CheckpointController,
	storeTicketMachines: some TicketMachine,
	storeProducts: some Item,
	//customers currently inside the store
	storeCustomersInStore: dynamicSet[Customer],
	//current queue for the store
	storeQueue: one Queue,
	//current bookings for the store
	storeBookings: dynamicSet[Booking],
	/* tickets that have been used to enter the store, but not necessarely
		to exit */
	storeUsedTickets: dynamicSet[Ticket],
	/* tickets that have not been used to enter the store, and are no more
		 valid */
	storeNotUsedInvalidTickets: dynamicSet[Ticket]
}{
	#storeControllers > 0
	#storeTicketMachines > 0
}

sig TicketMachine {
	machinePrintedTickets: dynamicSet[QueueTicket]
}

sig Category {}

sig Item {
	itemCategory: one Category
}

// bookings and queues
sig Booking {
	bookingTicket: one BookingTicket,
	bookingDateTime: one DateTime,
	bookingItems: set Item,
	bookingCategories: set Category
}

sig Queue {
	queueTickets: dynamicSet[QueueTicket],
} 

/************************
 *						*
 *						*
 *		  FACTS			*
 *						*
 *						*
 ************************/

/*-------------------------------------------------------------------------
	Ubiquity Facts: in this section we include facts stating that some
	entities cannot be shared by other entities.
	For instance: customers cannot be simoultaneously inside two stores
  -------------------------------------------------------------------------*/
/* No customer has superpowers that allow them to be in two stores at the
	same time */
fact noUbiquitySuperpowers{
	all t:Time | no disj s1,s2:Store |
		#(s1.storeCustomersInStore.t & s2.storeCustomersInStore.t) > 0
}

//No queue is owned by two stores
fact noSharedQueues{
	all  q:Queue | one s:Store | q in s.storeQueue
}

//No controller is owned by two stores
fact noSharedControllers{
	all  chk:CheckpointController | one s:Store | chk in s.storeControllers
}

//No ticket machine is shared by two stores
fact noSharedTicketMachine{
	all  tm:TicketMachine | one s:Store | tm in s.storeTicketMachines
}

//Each booking ticket is for one booking only
fact noSharedBookingTicket{
	all bt:BookingTicket | one b:Booking | b.bookingTicket = bt
}

//Every ticket is for only one store
fact ticketsAreForAtMostOneStore {
	all t: Ticket, time:Time | one s: Store |
		t in (s.storeUsedTickets.time + s.storeNotUsedInvalidTickets.time +
		s.storeBookings.time.bookingTicket + s.storeQueue.queueTickets.time)
}

//Every booking is for only one store
fact bookingsAreForAtMostOneStore {
	all b: Booking, t:Time| lone s: Store | b in s.storeBookings.t
}


fact ticketMustBeOnlyOfOneType {
	//tickets can either be:
	all t: Ticket, s: Store, time:Time |
		//used
		(t in s.storeUsedTickets.time implies
			t not in (s.storeNotUsedInvalidTickets.time + 
			s.storeQueue.queueTickets.time +
			s.storeBookings.time.bookingTicket))
		and
		//not used and invalid
		(t in s.storeNotUsedInvalidTickets.time implies
			t not in (s.storeUsedTickets.time + s.storeQueue.queueTickets.time
			+ s.storeBookings.time.bookingTicket))
		and
		//valid for booking
		(t in s.storeBookings.time.bookingTicket implies
			t not in (s.storeNotUsedInvalidTickets.time + 
			s.storeQueue.queueTickets.time + s.storeUsedTickets.time))
		and
		//valid for queueing
		(t in s.storeQueue.queueTickets.time implies
			t not in (s.storeNotUsedInvalidTickets.time +
			s.storeUsedTickets.time + s.storeBookings.time.bookingTicket))
}

//Tickets may be printed at most once
fact ticketMayBePrintedByAtMostOneTicketMachine {
	all t: Ticket, time:Time| lone tm: TicketMachine |
		t in tm.machinePrintedTickets.time
}

/* A customer cannot be in a queue and at the same time in the store owning
	that queue */
fact queueCannotContainInStoreCustomer {
	all s: Store, t:Time | no c: Customer |
		c in s.storeCustomersInStore.t and
		c in s.storeQueue.queueTickets.t.ticketOwner
}

/*---------------------------------------------------------------------
	No random changes : the following facts state that no new entities 
	appear in time unless an operation makes them appear.
	For instance, no new customer can appear in a store unless someone
	entered
----------------------------------------------------------------------*/
//A new customer appears iff someone enters or exits
fact CustomersDontMultiplyRandomly{
	all t:Time, s:Store | (some c:Customer |
		c in s.storeCustomersInStore.(t.next)
		and c not in s.storeCustomersInStore.(t) )
		iff
		((some qt:QueueTicket |enterStoreQueue[s,qt,t]) or
		(some b:Booking | enterStoreBooking[s,b,t]))
}

//A customer disappers iff somedy left the store
fact CustomersDontVanishRandomly{
	all t:Time, s:Store | (some c:Customer | c in  s.storeCustomersInStore.(t)
		and c not in s.storeCustomersInStore.(t.next) )
		iff
		( some tick:Ticket | leaveStore[s,tick,t])
}

//A ticket leaves a queue iff somebody left the queue or entered the store
fact queueticketsDontDisappearRandomly{
	all t:Time, s:Store |
		(some qt:QueueTicket |
			qt in  s.storeQueue.queueTickets.t and
			qt not in s.storeQueue.queueTickets.(t.next))
		iff
		(some qt:QueueTicket, c:Customer |
			leaveQueue[s.storeQueue,c, qt,t] or enterStoreQueue[s, qt,t ])
}

//A ticket appears in a queue iff somebody joined the queue
fact queueticketsDontAppearRandomly{
	all t:Time, s:Store |
		(some qt:QueueTicket |
			qt in  s.storeQueue.queueTickets.(t.next) and
			qt not in s.storeQueue.queueTickets.(t) )
				iff
			(some qt:QueueTicket, c:Customer | joinQueue[s.storeQueue,c,qt,t])
}

//Bookings appear iff a new visit is booked
fact bookingsDontAppearRandomly{
	all t:Time, s:Store |
		(some b:Booking|
			b in s.storeBookings.(t.next) and b not in s.storeBookings.(t) )
				iff
			( some b:Booking, c:Customer | bookVisit[s,b,c,t])
}

/*Bookings disappear iff a visit is deleted or somebody enters the store
	by using a booking */
fact bookingsDontAppearRandomly{
	all t:Time, s:Store |
		(some b:Booking|
			b in  s.storeBookings.(t) and b not in s.storeBookings.(t.next))
		iff
		(some b:Booking, c:Customer |
			deleteAVisit[s,c,b,t] or enterStoreBooking[s,b,t])
}

//A new control appears iff somebody entered the store
fact ControlsDontMultiplyRandomly{
	all t:Time, s:Store |
		(some tick:Ticket |
			tick in  s.storeControllers.controllerCheckIns.(t.next) and
			tick not in s.storeControllers.controllerCheckIns.t )
		iff
		( (some qt:QueueTicket |
			enterStoreQueue[s,qt,t]) or
			( some b:Booking | enterStoreBooking[s,b,t]) )
}

/*--------------------------------------------------------------------
	No Useless Entities: the following facts state that if 
	an entity exists, it must belong somewhere, i.e. we
	do not want isolted/useless entities. For instance, we can sureòy
	have unemployed Store Managers in real life, but they are not 
	relevant for our analysis, therefore we include these facts to 
	avoid their generation
----------------------------------------------------------------------*/
//Store managers manage at least one store
fact storeManagersManageAtLeastOneStore {
	all sm: StoreManager | some s: Store | sm in s.storeManagers
}

//Items are at least in one store
fact itemsAreAtLeastInOneStore {
	all i: Item | some s: Store | i in s.storeProducts
}

//Categories contain at least one item
fact categoriesContainsAtLeastOneItem {
	all c: Category | some i: Item | c = i.itemCategory
}


/* If tickets are printed, they are printed by a machine of the store they
	are for */
fact printedTicketsAreInQueueOrAreUsed {
	all t: Ticket , time:Time, s: Store |
		t in s.storeTicketMachines.machinePrintedTickets.time 
		implies
		(t in s.storeQueue.queueTickets.time or
		t in s.storeNotUsedInvalidTickets.time
		or t in s.storeUsedTickets.time)
}

//All used tickets have been checked at entrance
fact usedTicketsHaveBeenScanned {
	all t: Ticket, s: Store , time:Time|
		t in s.storeUsedTickets.time implies
		t in s.storeControllers.controllerCheckIns.time

	all t: Ticket, time:Time, s: Store |
		t in s.storeControllers.controllerCheckIns.time
		implies
		(t in s.storeUsedTickets.time or
		t in s.storeNotUsedInvalidTickets.time or
		t in s.storeBookings.time.bookingTicket)
}

/************************
 *						*
 *						*
 *		PREDICATES		*
 *						*
 *						*
 ************************/

//1. Join a queue
pred joinQueue[q:Queue, c:Customer, qt:QueueTicket, t:Time]{
	//preconditions
	//c owns the ticket
	qt.ticketOwner = c
	//the ticket is not already in the queue
	qt not in q.queueTickets.t
	//customer is not already in the queue
	no tick:QueueTicket |
		tick in q.queueTickets.t and tick.ticketOwner = c
	//the ticket must not have been used
	no chk:CheckpointController |
		qt in (chk.controllerCheckIns.t + chk.controllerCheckOuts.t)

	//postconditions
	//the ticket is now in the queue
	all ticket:QueueTicket |
		(ticket in q.queueTickets.(t.next))
		iff
		(ticket in q.queueTickets.t or ticket = qt)
	//the new ticket is greater than any other ticket in the queue
	all ticket:QueueTicket |
		ticket in q.queueTickets.(t) => lt[ticket,qt]
}

//2. Leave a queue
pred leaveQueue[q:Queue, c:Customer, qt:QueueTicket, t:Time]{
	//preconditions
	qt.ticketOwner = c
	qt in q.queueTickets.t
	//the ticket must not have been used
	no chk:CheckpointController |
		qt in (chk.controllerCheckIns.t + chk.controllerCheckOuts.t)
	
	//postconditions
	//the ticket is no longer in the queue
	all ticket:QueueTicket |
		(ticket in q.queueTickets.(t.next))
		iff
		(ticket in q.queueTickets.t and ticket != qt)
}

//3. Book a visit
pred bookVisit[s:Store, b:Booking, c:Customer, t:Time]{
	//preconditions
	/*the customer must own the new booking*/
	b.bookingTicket.ticketOwner = c
	/*the new booking cannot overlap with any already existing booking for s*/
	no ovlpBooking: Booking |
		ovlpBooking in s.storeBookings.t and
		ovlpBooking.bookingDateTime = b.bookingDateTime and  
		b.bookingTicket.ticketOwner = ovlpBooking.bookingTicket.ticketOwner
	/*the new booking cannot overlap with any already existing booking for
	any other store*/
	all s2:Store |
		s != s2 implies
		(no ovlpBooking: Booking |
			ovlpBooking.bookingTicket.ticketOwner = c and
			ovlpBooking.bookingDateTime = b.bookingDateTime and
			ovlpBooking in s2.storeBookings.t)

	//postconditions
	/*at time t.next, the store will only have the bookings that it had
		before + b*/
	all book:Booking |
		(book in s.storeBookings.(t.next))
		iff
		(book = b or book in s.storeBookings.t)
}

//4. Delete a visit
pred deleteAVisit[ s:Store, c:Customer, b:Booking, t:Time] {
	// preconditions
	/*b must be in the store before*/
	b in s.storeBookings.t
	/*b's customer must be c*/
	c = b.bookingTicket.ticketOwner
	
	// postconditions
	/*if a booking was in the store before and is different from b, it
	is in the store afterwards */
	all book:Booking |
		(book in s.storeBookings.t and book != b)
		iff
		book in s.storeBookings.(t.next)
	
}

//5.Enter a store from its queue
pred enterStoreQueue[s:Store, qt:QueueTicket, t:Time]{
	//preconditions
	/*entering customer is in the queue for s*/
	qt in s.storeQueue.queueTickets.t
	/*qt is the first of the queue*/
	all ticket:QueueTicket |
		(ticket in s.storeQueue.queueTickets.t and ticket != qt)
		implies
		lt[qt,ticket]
	/*the ticket must not have been used*/
	no chk:CheckpointController |
		qt in (chk.controllerCheckIns.t + chk.controllerCheckOuts.t)

	//postconditions
	/*the owner of the ticket is now in the store*/
	all c:Customer |
		c in s.storeCustomersInStore.(t.next)
		iff
		(c=qt.ticketOwner or c in s.storeCustomersInStore.t)
	/*the owner of the ticket is removed from the queue*/
	all ticket:QueueTicket |
		(ticket in s.storeQueue.queueTickets.(t.next))
		iff
		(ticket in s.storeQueue.queueTickets.t and ticket != qt)
	one chk:CheckpointController |
		qt in chk.controllerCheckIns.(t.next) and
		chk in s.storeControllers
	no chk:CheckpointController |
		qt in chk.controllerCheckIns.(t.next) and
		chk not in s.storeControllers
	all chk:CheckpointController |
		chk.controllerCheckOuts.(t.next) = chk.controllerCheckOuts.(t)
	all chk:CheckpointController |
		qt not in chk.controllerCheckIns.(t.next)
		iff
		chk.controllerCheckIns.(t.next) = chk.controllerCheckIns.(t) 
	all chk:CheckpointController |
		qt  in chk.controllerCheckIns.(t.next)
		iff
		chk.controllerCheckIns.(t.next) = chk.controllerCheckIns.(t) + qt
	
}

//6. Enter a store by booking
pred enterStoreBooking[s:Store, b:Booking, t:Time]{
	//preconditions
	/*is an active booking at the time of entering*/
	b in s.storeBookings.t
	/*the ticket related to b must not have been used*/
	no chk:CheckpointController |
		b.bookingTicket in (chk.controllerCheckIns.t +
			chk.controllerCheckOuts.t)

	//postconditions
	/*the booking is removed from the active bookings*/
	all book:Booking | book in s.storeBookings.(t.next)
		iff
		( book != b and book in s.storeBookings.t)
	/*the owner of the ticket is now in the store*/
	all c:Customer |
		c in s.storeCustomersInStore.(t.next)
		iff
		(c=b.bookingTicket.ticketOwner or c in s.storeCustomersInStore.t)
	one chk:CheckpointController |
		b.bookingTicket in chk.controllerCheckIns.(t.next) and
		chk in s.storeControllers and
		chk in s.storeControllers
	no chk:CheckpointController |
		b.bookingTicket in chk.controllerCheckIns.(t.next) and
		chk not in s.storeControllers
	all chk:CheckpointController |
		chk.controllerCheckOuts.(t.next) = chk.controllerCheckOuts.(t)
	all chk:CheckpointController |
		b.bookingTicket not in chk.controllerCheckIns.(t.next)
		iff
		chk.controllerCheckIns.(t.next) = chk.controllerCheckIns.(t) 
	all chk:CheckpointController |
		b.bookingTicket in chk.controllerCheckIns.(t.next)
		iff
		chk.controllerCheckIns.(t.next) = chk.controllerCheckIns.(t) + 
										  b.bookingTicket
}

//7.Leave a store
pred leaveStore[s:Store, tick:Ticket, t:Time]{
	//preconditions
	/*the owner of tick is in the store*/
	tick.ticketOwner in s.storeCustomersInStore.t
	tick in s.storeControllers.controllerCheckIns.t
	
	//postconditions
	/*the customer is no longer in the store*/
	all c:Customer |
		c in s.storeCustomersInStore.(t.next)
		iff
		( c != tick.ticketOwner and c in s.storeCustomersInStore.(t))
	/*customer has been checked at the exit*/
	one chk:CheckpointController |
		tick in chk.controllerCheckOuts.(t.next) and
		chk in s.storeControllers
	no chk:CheckpointController |
		tick in chk.controllerCheckOuts.(t.next) and
		chk not in s.storeControllers
	all chk:CheckpointController |
		chk.controllerCheckIns.(t.next) = chk.controllerCheckIns.(t)
	all chk:CheckpointController |
		tick not in chk.controllerCheckOuts.(t.next)
		implies
		chk.controllerCheckOuts.(t.next) = chk.controllerCheckOuts.(t) 
	all chk:CheckpointController |
		tick  in chk.controllerCheckOuts.(t.next)
		implies
		chk.controllerCheckOuts.(t.next) = chk.controllerCheckOuts.(t) + tick
}

//8. Print a ticket for a store
pred printTicket[s:Store, qt:QueueTicket ,c:Customer, t:Time]{
	//preconditions
	qt.ticketOwner = c
	c not in s.storeCustomersInStore.t
	qt not in s.storeTicketMachines.machinePrintedTickets.t
	qt not in s.storeQueue.queueTickets.t
	qt not in s.storeControllers.controllerCheckIns.t
	qt not in s.storeControllers.controllerCheckOuts.t

	//postconditions
	s.storeTicketMachines.machinePrintedTickets.(t.next) =
		s.storeTicketMachines.machinePrintedTickets .t + qt
	s.storeQueue.queueTickets.(t.next) = s.storeQueue.queueTickets.t + qt
	all qn1: QueueTicket |
		(qn1 in s.storeQueue.queueTickets.(t.next) and qn1 != qt )
		implies
		lt[qn1, qt]
}

/************************
 *						*
 *						*
 *		AUXILIARY		*
 *		PREDICATES		*
 *						*
 *						*
 ************************/

pred checkoutSubsetCheckin[s:Store, t:Time]{
	 s.storeControllers.controllerCheckOuts.t
		in
	s.storeControllers.controllerCheckIns.t
}

pred storeOutSubsetIns[s:Store, t:Time]{
	s.storeControllers.controllerCheckOuts.t
		in
	s.storeControllers.controllerCheckIns.t
}

pred noCustomerAppearsTwice[q:Queue, t:Time]{
	no disj qt1, qt2: QueueTicket |
		qt1 in q.queueTickets.t and
		qt2 in q.queueTickets.t and
		qt1.ticketOwner = qt2.ticketOwner
}

pred disjointQueues[q1,q2:Queue, t:Time]{
	
	no c:Customer |
		c in q1.queueTickets.t.ticketOwner and
		c in q2.queueTickets.t.ticketOwner
}

pred allGuestsChecked[s:Store, t:Time]{
	all c:Customer |
		c in s.storeCustomersInStore.t
		implies
		(some chk:CheckpointController |
			c in chk.controllerCheckIns.t.ticketOwner)
}

pred hasOverlappingBooking[ s:Store, t:Time]{
	some disj b1,b2:Booking |
		b1 in s.storeBookings.t and
		b2 in s.storeBookings.t and
		b1.bookingDateTime = b2.bookingDateTime and
		b1.bookingTicket.ticketOwner = b2.bookingTicket.ticketOwner
}

pred haveOverlappingBooking[ s1,s2:Store, t:Time]{
	some disj b1,b2:Booking |
		b1 in s1.storeBookings.t and
		b2 in s2.storeBookings.t and
		b1.bookingDateTime = b2.bookingDateTime and
		b1.bookingTicket.ticketOwner = b2.bookingTicket.ticketOwner
}

pred checkedInButNotOut[c:Customer, s:Store, t:Time]{
	some tick:Ticket |
		tick.ticketOwner = c and
		tick in s.storeControllers.controllerCheckIns.t and
		tick not in s.storeControllers.controllerCheckOuts.t
}

/************************
 *						*
 *						*
 *		ASSERTIONS		*
 *						*
 *						*
 ************************/
/* Our assertions are aimed at proving that the operations that were defined
	in the predicates do not alter the consistency of a state.
	At first, we prove that the chosen property is respected in a basic case.
	Then, we show that if we are in a state that respects the property, and
	we perform some operation on the entity we are working with, the state in
	the following time will also respect such property.
	For more details, please check the reference section.
*/

/*This assertion proves that at any time and for every controller, the
	tickets that they checkedOut are a subset of those they checkedIn */
assert CheckoutSubsetCheckin{
	/*Base Case: if no one was controlled for a store S, the property holds*/
	all s:Store, t:Time |
		#s.storeControllers.controllerCheckOuts.t = 0 and
		#s.storeControllers.controllerCheckIns.t = 0
			implies
		storeOutSubsetIns[s,t]

	/*Inductive Steps: if we start from a consistent state, and some
	customer enters the Store or leaves it, the property still holds*/
	all s:Store, t:Time |
		storeOutSubsetIns[s,t] and
		(some qt:QueueTicket | enterStoreQueue[s,qt,t])
			implies
		storeOutSubsetIns[s,t.next]
	all s:Store, t:Time |
		storeOutSubsetIns[s,t] and
		(some b:Booking| enterStoreBooking[s,b,t])
			implies
		storeOutSubsetIns[s,t.next]
	all s:Store, t:Time |
		storeOutSubsetIns[s,t] and
		(some tick:Ticket | leaveStore[s,tick,t])
			implies
		storeOutSubsetIns[s,t.next]
}

//This assertion proves that no customer can appear twice in the same queue
assert NoCustomerTwiceSameQueue{
	/*Base Case: the property holds for an empty queue*/
	all q:Queue, t:Time |
		#q.queueTickets.t = 0
		implies
		noCustomerAppearsTwice[q,t]

	/*Inductive Steps: if we start from a consistent queue and some customer
	joins the queue or leaves it, the property still holds*/
	all q:Queue, t:Time |
		noCustomerAppearsTwice[q,t] and
		(some c:Customer, qt:QueueTicket | joinQueue[q,c,qt,t])
			implies
		noCustomerAppearsTwice[q,t.next]
	all q:Queue, t:Time |
		noCustomerAppearsTwice[q,t] and
		(some c:Customer, qt:QueueTicket | leaveQueue[q,c,qt,t])
			implies
		noCustomerAppearsTwice[q,t.next]
}

//This assertion proves that no customer can be twice in different queues
assert NoTwoQueuesShareCustomer{
	/*Base Case: the property holds for two empty queues*/
	all disj q1,q2:Queue , t:Time |
		#q1.queueTickets=0 and
		#q2.queueTickets=0
			implies
		disjointQueues[q1,q2,t]

	/*Inductive Steps: if we start from two consistent queue sand some
	customer joins on of the queues or leaves it, the property still holds*/
	all disj q1,q2:Queue , t:Time |
		disjointQueues[q1,q2,t] and
		(some c:Customer, qt:QueueTicket | joinQueue[q1,c,qt,t])
			implies
		disjointQueues[q1,q2,t.next]
	all disj q1,q2:Queue , t:Time |
		disjointQueues[q1,q2,t] and
		(some c:Customer, qt:QueueTicket | leaveQueue[q1,c,qt,t])
			implies
		disjointQueues[q1,q2,t.next]
}

/*This assertion proves that any customer that is inside the store was
	checkedIn at some point*/
assert NoUncheckedGuest{
	/*Base Case: the property holds for an empty store*/
	all s:Store, t:Time |
		#s.storeCustomersInStore = 0
		implies
		allGuestsChecked[s,t]
	
	/*Inductive Steps: if we start from a consistent state, and some
	customer enters the Store or leaves it, the property still holds*/
	all s:Store, t:Time |
		allGuestsChecked[s,t] and
		(some qt:QueueTicket | enterStoreQueue[s,qt,t])
			implies
		allGuestsChecked[s,t.next]
	all s:Store, t:Time |
		allGuestsChecked[s,t] and
		(some b:Booking| enterStoreBooking[s,b,t])
			implies
		allGuestsChecked[s,t.next]
	all s:Store, t:Time |
		allGuestsChecked[s,t] and
		(some tick:Ticket| leaveStore[s,tick,t])
			implies
		allGuestsChecked[s,t.next]
}

//This assertion proves that a store cannot have two overlapping bookings
assert NoOverlappingBookingSameStore{
	/*Base Case: the property holds for an Store without bookings*/
	all s:Store, t:Time |
		#s.storeBookings.t = 0
		implies
		!hasOverlappingBooking[s,t]
	
	/*Inductive Steps: if we start from a consistent state, and some visit
	is either booked or deleted, the property still holds*/
	all s:Store, t:Time |
		!hasOverlappingBooking[s,t] and
		(some c:Customer,b:Booking | bookVisit[s, b,c,t])
			implies
		!hasOverlappingBooking[s,t]
	all s:Store, t:Time |
		!hasOverlappingBooking[s,t] and
		(some c:Customer,b:Booking | deleteAVisit[s, c,b,t])
			implies
		!hasOverlappingBooking[s,t]
}

//This assertion proves that no two stores can have overlapping bookings
assert NoOverlappingBookingDiffStore{
	/*Base Case: the property holds for two stores both without a booking*/
	all s1,s2:Store, t:Time |
		#s1.storeBookings.t = 0 and
		#s2.storeBookings.t = 0
			implies
		!haveOverlappingBooking[s1,s2,t]
	
	/*Inductive Steps: if we start from a consistent state, and some visit
	is either booked or deleted, the property still holds*/
	all s1,s2:Store, t:Time |
		!haveOverlappingBooking[s1,s2,t] and
		(some c:Customer,b:Booking | bookVisit[s1, b,c,t])
			implies
		!haveOverlappingBooking[s1,s2,t]
	all s1,s2:Store, t:Time |
		!haveOverlappingBooking[s1,s2,t] and
		(some c:Customer,b:Booking | deleteAVisit[s1, c,b,t])
			implies
		!haveOverlappingBooking[s1,s2,t]
}

/*This assertion proves that if a customer is inside a store it has some
	ticket that was checked in but not checkedout*/
assert ControllersWorkProperly{
	/*Base Case: the property holds for an empty store*/
	all s:Store, t:Time |
		#s.storeCustomersInStore.t = 0
		implies
		( all c:Customer |
			c in s.storeCustomersInStore.t
			implies
			checkedInButNotOut[c,s,t])
	
	/*Inductive Steps: if we start from a consistent state, and some
	customer enters the Store or leaves it, the property still holds*/
	all s:Store, t:Time |
		( all c:Customer |
			c in s.storeCustomersInStore.t
			implies checkedInButNotOut[c,s,t]) and 
		(some qt:QueueTicket | enterStoreQueue[s,qt,t])
			implies
		(all c:Customer |
			c in s.storeCustomersInStore.t
			implies checkedInButNotOut[c,s,t.next])
	
	all s:Store, t:Time |
		( all c:Customer |
			c in s.storeCustomersInStore.(t.next)
			implies checkedInButNotOut[c,s,t]) and 
		(some b:Booking|
			enterStoreBooking[s,b,t])
			implies
			(all c:Customer |
				c in s.storeCustomersInStore.(t.next)
				implies checkedInButNotOut[c,s,t.next])

	all s:Store, t:Time |
		( all c:Customer |
			c in s.storeCustomersInStore.t
			implies checkedInButNotOut[c,s,t]) and 
		(some tick:Ticket| leaveStore[s,tick,t])
			implies
		(all c:Customer |
			c in s.storeCustomersInStore.(t.next)
			implies checkedInButNotOut[c,s,t.next])
}

pred show{}
run show for 4 but exactly 2 Store, exactly 2 Queue


/***************
*	Run Predicates	*
***************/
run joinQueue for 7 but
	exactly 2 Store, exactly 2 Queue, exactly 6 QueueTicket,
	exactly 4 Time, exactly 2 CheckpointController
run leaveQueue for 7 but
	exactly 1 Store, exactly 1 Queue, exactly 6 QueueTicket,
	exactly 4 Time, exactly 2 CheckpointController
run bookVisit  for 7 but
	exactly 2 Store, exactly 2 Queue, exactly 6 QueueTicket,
	exactly 4 Time, exactly 2 CheckpointController, exactly 3 Booking,
	exactly 3 BookingTicket
run deleteAVisit  for 7 but
	exactly 1 Store, exactly 1 Queue, exactly 6 QueueTicket,
	exactly 5 Time, exactly 2 CheckpointController, exactly 3 Booking,
	exactly 3 BookingTicket
run enterStoreQueue for 7 but
	exactly 1 Store, exactly 1 Queue, exactly 6 QueueTicket,
	exactly 4 Time, exactly 2 CheckpointController, exactly 4 Customer
run enterStoreBooking for 7 but
	exactly 1 Store, exactly 1 Queue, exactly 6 QueueTicket,
	exactly 4 Time, exactly 2 CheckpointController, exactly 3 Booking,
	exactly 3 BookingTicket
run leaveStore for 7 but
	exactly 1 Store, exactly 1 Queue, exactly 6 QueueTicket,
	exactly 4 Time, exactly 2 CheckpointController, exactly 4 Customer
run printTicket for 7 but
	exactly 1 Store, exactly 1 Queue, exactly 6 QueueTicket,
	exactly 4 Time, exactly 2 CheckpointController, exactly 4 Customer

/***************
*	Run Assertions	*
***************/
check CheckoutSubsetCheckin
check NoCustomerTwiceSameQueue
check NoTwoQueuesShareCustomer
check NoUncheckedGuest
check NoOverlappingBookingSameStore
check NoOverlappingBookingDiffStore
check ControllersWorkProperly
