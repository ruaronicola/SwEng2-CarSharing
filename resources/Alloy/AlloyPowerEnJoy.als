module PowerEnJoy
open utils/boolean


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
	license: lone License,
	isLocked: one Bool
}

// we can assume that we are just modelling an instant in time without considering the previous user actions, otherwise virtuous/bad users are inconsistent as actors as a user can be both virtuous and bad
// ok.. maybe is nonsense modelling users as virtuous/bad.. that should be just an abstract behaviour..
// so, alternatively we can model start/end time as Ints and check intervals for overlapping
// but be careful..! use cases and so on should be adapted
abstract sig BillType {}
one sig EXPIRATION_BILL, STD_BILL, DISCOUNT_BILL, FEE_BILL extends BillType {}
sig Bill {
	type: one BillType
	payedBy: one User
//	payedTime: one Int
}

abstract sig Event {
	startTime: one Int,
	endTime: lone Int
}{endTime>startTime
	startTime>0
	endTime>0}

sig Reservation extends Event{
	user: one User,
	vehicle: one Vehicle,
	isExpired: one Bool,
	bill: lone Bill
}{
	active implies not isExpired
	isExpired implies not active //forse isActive ci va?
	bill.type=EXPIRATION_BILL
}

sig Ride extends Event{
	reservation: one Reservation,
	startPosition: one Position,
	endPosition: lone Position,
	bill: one Bill
	otherTwoOrMorePassengers: one Bool
}{
	not(bill=null) implies not(endPosition=null)
	(endPosition=null) implies (bill=null)
	startPosition in SafeArea.positions
	bill.type!=EXPIRATION_BILL
	(!(isActive) and (endPosition !=SafeArea.position)) implies (bill.type= FEE_BILL)
	(!(isActive) and (reservation.vehicle.batteryLevel=LOW) implies (bill.type= FEE_BILL)
	reservation.vehicle.category=B_CATEGORY //per ora che ci sono solo auto.
}


// FACTS

fact NoDoubleReservations {
	no r1:Reservation | some r2:Reservation | overlap[r1, r2] and r1.user=r2.user 
	no r1:Reservation | some r2:Reservation | overlap[r1, r2] and r1.vehicle=r2.vehicle
}

fact NoDoublePayment{
	no b1:Bill | some b2: Bill | b1.payedBy=b2.payedBy
}

fact NoDoubleRide{
	no r1:Ride | some r2:Ride|overlap[r1,r2] and r1.reservation=r2.reservation
	//no r1:Ride | some r2:Ride | overlap[r1, r2] and r1.reservation.car=r2.reservation.car   --ripetizione
}	


fact LicenseMatchesVehicle {
	no r:Reservation | not (r.car.category in r.user.licence.categories)
}

fact NoRandomRide {
	no r:Ride |  isActive[r.reservation]
	no r:Ride |  r.reservation.isExpired
}

fact NoLockedUserAction {
	no r:Reservation | r.user.isLocked
}

fact VehicleStateConsistency {
	all v:Vehicle | all r:Ride | r.reservation.vehicle=v | (not isActive[r]) and (not isActive[r.reservation]) <=> v.state = FREE
	all v:Vehicle | some r:Reservation | r.vehicle=v | isActive[r] <=> v.state = RESERVED
	all v:Vehicle | some r:Ride | r.reservation.vehicle=v | isActive[r] <=> v.state = IN_USE
	
}
// keep track of bills and discounts/charges based upon final car state after a ride.. (//additionalPassengers: one Bool.. additionalPassenger)


// PREDICATES

pred isActive [e: Event]{
	#e.endTime=0
}

pred overlap [e1,e2: Event]{
	e1.startTime<e2.startTime<e1.endTime or 
	e2.startTime<e1.startTime<e2.endTime or
	isActive[e1] and isActive[e2]
}

pred show {}


run show for 10

