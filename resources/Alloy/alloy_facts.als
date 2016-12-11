// FACTS

// all reservations are assigned to at most one ride and have coherent user/vehicle
fact ReservationMatchRide {
	no disj r1,r2:Ride | r1.reservation=r2.reservation 
    all ride:Ride | ride.user=ride.reservation.user
	all ride:Ride | ride.vehicle=ride.reservation.vehicle
}

// no more active events from the same user
fact NoEventOverlap {
	no disj e1, e2:Event | overlap[e1, e2] and e1.user=e2.user 
	no disj e1, e2:Event | overlap[e1, e2] and e1.vehicle=e2.vehicle 
}

// all licenses belong to one user
fact LicenseMatchUser {
	all l:License | one u:User | u.license=l
}

// users cannot reserve/drive vehicles without the correct license 
fact LicenseMatchVehicle {
	all e:Event | e.vehicle.category in e.user.license.categories
}

// all rides must have a valid reservation associated
fact NoRandomRide {
	no r:Ride | isActive[r.reservation]
	no r:Ride | r.reservation.isExpired=True
	all ride:Ride | ride.startTime>=ride.reservation.endTime
}

// banned users cannot reserve/drive cars
fact NoLockedUserAction {
	no e:Event | isActive[e] and e.user.isLocked=True
}

// vehicle state should be consistent
fact VehicleStateConsistency {
	all v:Vehicle | v.state=FREE or v.state=OUT_OF_SERVICE <=> 
						(no e:Event | e.vehicle=v and isActive[e])
	all v:Vehicle | v.state=RESERVED <=> 
						(one r:Reservation | r.vehicle=v and isActive[r])
	all v:Vehicle | v.state=IN_USE <=> 
						(one r:Ride | r.vehicle=v and isActive[r])
}

// all bills are assigned to a single ride or reservation
fact NoRandomBill {
	no disj r1,r2:Ride | #r1.bill=1 and #r2.bill=1 and r1.bill=r2.bill
	no disj r1,r2:Reservation | #r1.bill=1 and #r2.bill=1 and r1.bill=r2.bill
	no r1:Ride, r2:Reservation | #r1.bill=1 and #r2.bill=1 and r1.bill=r2.bill
	no b:Bill | no r1:Ride, r2:Reservation |  (#r1.bill=1 and r1.bill=b) or 
											  (#r2.bill=1 and r2.bill=b)
}

//if a vehicle is charging is in a charging station
fact ConsistentCharging {
	all v:Vehicle | v.plugged=True implies 
					(some c:ChargingStation | c.position=v.position)  
}

//if vehicle was used its position should match with last ride endPosition
fact ConsistentVehiclePosition {
	all v:Vehicle | (some r:Ride | r.vehicle=v) implies 
					(some r1:Ride | isLast[r1] and (r1.endPosition=v.position))  
}

//if vehicle was used its plugging state should match with last ride plugging state
fact ConsistentVehiclePlugging {
	all r:Ride | some c:ChargingStation | r.hasLeftPlugged=True implies 
										  r.endPosition=c.position
	all v:Vehicle | (some r:Ride | r.vehicle=v) implies 
					(some r1:Ride | isLast[r1] and 
									(r1.hasLeftPlugged=True <=> 
									 v.plugged=True))
}

//if vehicle was used its batteryLevel should match with last ride batteryLevel
fact ConsistentVehicleBattery {
	all v:Vehicle | (some r:Ride | r.vehicle=v) implies 
					(some r1:Ride | isLast[r1] and 
									(r1.hasLeftHighBattery=True <=> 
									 v.batteryLevel=HIGH))
	all v:Vehicle | (some r:Ride | r.vehicle=v) implies 
					(some r1:Ride | isLast[r1] and
									(r1.hasLeftLowBattery=True <=> 
									 v.batteryLevel=LOW))
	all v:Vehicle | (some r:Ride | r.vehicle=v) implies 
					(some r1:Ride | isLast[r1] and 
									(r1.hasLeftHighBattery=False and 
									 r1.hasLeftLowBattery=False <=> 
									 v.batteryLevel=MEDIUM))
}



// no two distinct objects with the same position
fact ConsistentPosition {
	no disj v1,v2:Vehicle | v1.position = v2.position
	no disj c1,c2:ChargingStation | c1.position = c2.position
}
