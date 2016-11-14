// PREDICATES

pred isActive [e: Event]{
	#e.endTime=0
}

pred overlap [e1,e2: Event]{
	e1.startTime<=e2.startTime and e2.startTime<=e1.endTime or 
	e2.startTime<=e1.startTime and e1.startTime<=e2.endTime or
	isActive[e1] and isActive[e2]
}

pred isLast [r:Ride] {
	all r2:Ride | r2!=r and r2.vehicle=r.vehicle implies r2.endTime<r.endTime
}

pred show {
	#Ride>1
	some expired:Reservation | expired.isExpired=True
}


run show for 3 but 5 Event
