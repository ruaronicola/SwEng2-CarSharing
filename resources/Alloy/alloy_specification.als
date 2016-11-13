module PowerEnJoy


// SIGNATURES 

abstract sig Bool{}
one sig True, False extends Bool {}

abstract sig Category {}
one sig A_CATEGORY, B_CATEGORY extends Category {}

// assumptions on consistency of states
abstract sig State {}
one sig FREE, RESERVED, IN_USE, OUT_OF_SERVICE extends State {}

sig Position {}
one sig SafeArea {
	coverage: set Position
}{#coverage>0}
//some sig ChargingStation in SafeArea{
//	recharge: set Position
//}(#recharge>0)


abstract sig BatteryLevel {}
one sig LOW, MEDIUM, HIGH extends BatteryLevel {}

abstract sig Vehicle {
	category: one Category,
	state: one State,
	position: one Position,
	batteryLevel: one BatteryLevel,
	charging: one Bool //if a car is charging it's in a charge staton!
}{
	batteryLevel = LOW implies state = OUT_OF_SERVICE
	not (position in SafeArea.coverage) implies (state = OUT_OF_SERVICE)
	charging=True implies ( position in SafeArea.coverage)
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
	#bill=1 <=> isExpired=True 
	#bill=1 implies bill.type=EXPIRATION_BILL
}

sig Ride extends Event{
	reservation: one Reservation,
	startPosition: one Position,
	endPosition: lone Position,
	hasAdditionalPassengers: one Bool,
	hasLeftLowBattery: one Bool,
	hasLeftHighBattery: one Bool,
	bill: lone Bill
}{
	startPosition in SafeArea.coverage
	startPosition!=endPosition
	#bill=1 or #endPosition=1 <=> not isActive[this]
	#bill=1 <=> #endPosition=1
	bill.type!=EXPIRATION_BILL
	
	bill.type=DISCOUNT_BILL <=> not isActive[this] and ( (endPosition in SafeArea.coverage) and (hasAdditionalPassengers=True) )
	bill.type=DISCOUNT_BILL <=> not isActive[this] and ((endPosition  in SafeArea.coverage) and ( vehicle.charging= True ))
	bill.type=DISCOUNT_BILL <=> not isActive[this] and ( (endPosition in SafeArea.coverage) and(hasLeftHighBattery= True )	)
	bill.type=STD_BILL =>  not isActive[this] and (endPosition in SafeArea.coverage)
	bill.type=FEE_BILL <=>  not isActive[this] and (( not (endPosition in SafeArea.coverage) )or (hasLeftLowBattery=True) ) 
}


// FACTS

fact ReservationMatchRide {
	all res:Reservation | lone ride:Ride | ride.reservation=res
    all ride:Ride | ride.user=ride.reservation.user
	all ride:Ride | ride.vehicle=ride.reservation.vehicle
}

fact NoEventOverlap {
	no disj e1, e2:Event | overlap[e1, e2] and e1.user=e2.user 
	no disj e1, e2:Event | overlap[e1, e2] and e1.vehicle=e2.vehicle 
}

fact LicenseMatchUser {
	all l:License | one u:User | u.license=l
}

fact LicenseMatchVehicle {
	all e:Event | e.vehicle.category in e.user.license.categories
}

fact NoRandomRide {
	no r:Ride | isActive[r.reservation]
	no r:Ride | r.reservation.isExpired=True
	all ride:Ride | ride.startTime>=ride.reservation.endTime
}

fact NoLockedUserAction {
	no r:Reservation | isActive[r] and r.user.isLocked=True
}

fact VehicleStateConsistency {
	all v:Vehicle | all r:Ride | r.reservation.vehicle=v implies ( (not isActive[r]) and (not isActive[r.reservation]) <=> v.state = FREE )
	all v:Vehicle | one r:Reservation | r.vehicle=v implies ( isActive[r] <=> v.state = RESERVED )
	all v:Vehicle | one r:Ride | r.reservation.vehicle=v implies ( isActive[r] <=> v.state = IN_USE )
}

fact NoRandomBill {
	all b:Bill | one r1:Reservation, r2:Ride | r1.bill=b or r2.bill=b
}

fact ConsistentVehiclePosition {
	all v:Vehicle | (some r:Ride | r.vehicle=v) implies (some r1:Ride | r1.endPosition=v.position and (all r2:Ride | r2!=r1 and r2.vehicle=r1.vehicle implies r2.endTime<r1.endTime))  //if vehicle was used its position should match with last ride endPosition
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

