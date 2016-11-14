module PowerEnJoy


// SIGNATURES 

abstract sig Bool{}
one sig True, False extends Bool {}

abstract sig Category {}
one sig A_CATEGORY, B_CATEGORY extends Category {}

abstract sig State {}
one sig FREE, RESERVED, IN_USE, OUT_OF_SERVICE extends State {}

sig Position {}
one sig SafeArea {
	coverage: set Position
}{#coverage>0}

sig ChargingStation {
	position: Position
}{position in SafeArea.coverage}

abstract sig BatteryLevel {}
one sig LOW, MEDIUM, HIGH extends BatteryLevel {}

abstract sig Vehicle {
	category: one Category,
	state: one State,
	position: one Position,
	batteryLevel: one BatteryLevel,
	plugged: one Bool
}{
	batteryLevel = LOW implies state = OUT_OF_SERVICE 
	not (position in SafeArea.coverage) implies state=OUT_OF_SERVICE
	plugged=True implies ( position in SafeArea.coverage)
}
sig Car extends Vehicle{}{category=B_CATEGORY}

sig License{
	categories: set Category
}{#categories>0}

sig User {
	license: one License,
	isLocked: one Bool
}

abstract sig BillType {}
one sig EXPIRATION_BILL, STD_BILL, DISCOUNT_BILL, FEE_BILL extends BillType {}  
sig Bill {
	type: one BillType,
	payed: one Bool   
}

abstract sig Event {
	user: one User,
	vehicle: one Vehicle,
	startTime: one Int,
	endTime: lone Int
}{
	startTime>0
	#endTime=1 implies endTime>startTime
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
	hasLeftPlugged: one Bool,
	bill: lone Bill
}{
	startPosition in SafeArea.coverage
	startPosition!=endPosition
	hasLeftHighBattery=True <=> not hasLeftLowBattery=True
	#bill=1 <=> #endPosition=1
	#endPosition=1 <=> not isActive[this]
	bill.type!=EXPIRATION_BILL
 	bill.type=DISCOUNT_BILL <=> not isActive[this] and 
 								(endPosition in SafeArea.coverage) and 
 								(hasAdditionalPassengers=True or 
 								 hasLeftHighBattery=True or 
 								 hasLeftPlugged=True)
 	bill.type=FEE_BILL <=> not isActive[this] and 
 						   not bill.type=DISCOUNT_BILL and 
 						   (not(endPosition in SafeArea.coverage) or 
 						   	hasLeftLowBattery=True)
	bill.type=STD_BILL <=> not isActive[this] and 
						   not bill.type=DISCOUNT_BILL and 
						   not bill.type=FEE_BILL
}
