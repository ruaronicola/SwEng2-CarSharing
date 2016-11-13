module PowerEnJoy
open util/boolean


// SIGNATURES 

abstract sig Category {}
one sig A_CATEGORY, B_CATEGORY extends Category {}

// assumptions on consistency of states
abstract sig State {}
one sig FREE, RESERVED, IN_USE, OUT_OF_SERVICE extends State {}

sig Position {}
one sig SafeArea {
	positions: set Position
}{#positions>0}

abstract sig BatteryLevel {}
one sig LOW, MEDIUM, HIGH extends BatteryLevel {}

abstract sig Vehicle {
	category: one Category,
	state: one State,
	position: one Position,
	batteryLevel: one BatteryLevel
}{
	batteryLevel = LOW implies state = OUT_OF_SERVICE
	not (position in SafeArea.positions) implies (state = OUT_OF_SERVICE)
}
sig Car extends Vehicle{}{category=B_CATEGORY}

sig License{
	categories: set Category
}{#categories>0}

sig User {
	license: one License,
	isLocked: one Bool
}

// we can assume that we are just modelling an instant in time without considering the previous user actions, otherwise virtuous/bad users are inconsistent as actors as a user can be both virtuous and bad
// ok.. maybe is nonsense modelling users as virtuous/bad.. that should be just an abstract behaviour..
// so, alternatively we can model start/end time as Ints and check intervals for overlapping
// but be careful..! use cases and so on should be adapted
abstract sig BillType {}
one sig EXPIRATION_BILL, STD_BILL, DISCOUNT_BILL, FEE_BILL extends BillType {}  //assume some kind of precedence between special rates
sig Bill {
	type: one BillType,
	payed: one Bool   // assume that bills are payed once and correctly handled by payment handler
}

abstract sig Event {
	user: one User,
	vehicle: one Vehicle,
	startTime: one Int,
	endTime: lone Int
}{
	startTime>0
	endTime>0
	endTime>startTime
}

sig Reservation extends Event{
	isExpired: one Bool,
	bill: lone Bill
}{
	isActive[this] implies isExpired=False
	isExpired=True implies not isActive[this]
    isActive[this] implies vehicle.state=RESERVED
	bill.type=EXPIRATION_BILL
}

sig Ride extends Event{
	reservation: one Reservation,
	startPosition: one Position,
	endPosition: lone Position,
	hasAdditionalPassengers: one Bool,
	hasLeftLowBattery: one Bool,
	bill: lone Bill
}{
	startPosition in SafeArea.positions
	#bill=1 <=> #endPosition=1
	isActive[this] <=> #bill=0 and #endPosition=0
	#bill=1 implies bill.type!=EXPIRATION_BILL
    bill.type=FEE_BILL <=> !isActive[this] and ( (endPosition not in SafeArea.positions) or (hasLeftLowBattery=True) )
	bill.type=DISCOUNT_BILL <=> !isActive[this] and ( (hasAdditionalPassengers=True) )
}


// FACTS

fact ReservationMatchRide {
    all ride:Ride | ride.user=ride.reservation.user
	all ride:Ride | ride.vehicle=ride.reservation.vehicle
}

fact NoDoubleEvent {
	no e1:Event | some e2:Event | overlap[e1, e2] and e1.user=e2.user 
	no e1:Event | some e2:Event | overlap[e1, e2] and e1.vehicle=e2.vehicle 
}

fact LicenseMatchesVehicle {
	no r:Reservation | not (r.vehicle.category in r.user.license.categories)
}

fact NoRandomRide {
	no r:Ride | isActive[r.reservation]
	no r:Ride | r.reservation.isExpired=True
}

fact NoLockedUserAction {
	no r:Reservation | isActive[r] and r.user.isLocked=True
}

fact VehicleStateConsistency {
	all v:Vehicle | all r:Ride | r.reservation.vehicle=v implies (not isActive[r]) and (not isActive[r.reservation]) <=> v.state = FREE
	all v:Vehicle | some r:Reservation | r.vehicle=v implies isActive[r] <=> v.state = RESERVED
	all v:Vehicle | some r:Ride | r.reservation.vehicle=v implies isActive[r] <=> v.state = IN_USE
	
}

fact NoRandomBill {
	all b:Bill | some r1:Reservation, r2:Ride | r1.bill=b or r2.bill=b
}

// keep track of bills and discounts/charges based upon final car state after a ride.. (//additionalPassengers: one Bool.. additionalPassenger)


// PREDICATES

pred isActive [e: Event]{
	#e.endTime=0
}

pred overlap [e1,e2: Event]{
	e1.startTime<e2.startTime and e2.startTime<e1.endTime or 
	e2.startTime<e1.startTime and e1.startTime<e2.endTime or
	isActive[e1] and isActive[e2]
}

pred show {}


run show for 3 but 2 Bill

