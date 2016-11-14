open util/integer as integer

//--------------------------------------------------------------- SIG --------------------------------------------------------

//Geographical position (simplified in this model using pair of Int instead of Float)
sig Position{
	lat: one Int,
	lon: one Int
}

//Container of all positions recognized by our system
sig Map{
	area : some Position
}

/*
The set of safe areas for parking cars is predefined by the management system (sig Company).
Areas can have any shape: we'll consider them as a predefined set of Positions.
We assume there is at least one safe area.
*/

abstract sig SafeArea extends Map{}

sig ParkingArea extends SafeArea{}

abstract sig PlugStatus{}
sig P_Reserved, P_Available, P_InUse extends PlugStatus{} //reserved if user has a MSO enabled

sig Plug{
	status : one PlugStatus,
	pluggedCar : lone Car
} {
	status = P_InUse implies pluggedCar != none
	pluggedCar != none implies status = P_InUse
}

// We assume that charging stations in our model all have at least one working plug

sig ChargingStation extends SafeArea{
	plugs : some Plug
}{
	#(area) = #(plugs)
	all c : Car | c in plugs.pluggedCar implies c.pos in area
}

fact {
	no disjoint c1, c2 : ChargingStation | some p : Plug | p in c1.plugs and p in c2.plugs
}

sig Plate{}

sig Seat{}

abstract sig CarStatus{}
sig Available, Charging, Reserved extends CarStatus{}
sig Used, TemporaryBreak extends Reserved{}

abstract sig BatteryLevel{}
sig MoreThanHalf, ChargeNeeded /*<=20%*/ , OtherBatteryLevel extends BatteryLevel{} 

abstract sig MotorStatus{}
sig On, Off extends MotorStatus{}

abstract sig CarDoors{}
sig Locked, Unlocked extends CarDoors{}

sig Car{
	plate : one Plate,
	battery : one BatteryLevel,
	status: one CarStatus,
	doors: one CarDoors,
	pos : one Position,
	motor: one MotorStatus,
	seats : set Seat
}{
	#seats >= 2
	(doors = Locked or status = Charging or status = TemporaryBreak  ) implies motor = Off
	(status = Charging or status = Available) implies doors = Locked
	status = Available implies pos in SafeArea.area
	motor = On implies doors = Unlocked
}

one sig Company{
	cars: set Car,
	parkingAreas : set ParkingArea,
	stations : set ChargingStation,
	users : set User,
	costPerMinute : one Int,
}{
	costPerMinute > 0
}

sig ReservationCode{}

sig Licence{}


sig User{
	licenceNumber : one Licence,
	curRes : lone Reservation, 
	ride : lone Ride,
	bills : set Bill
} {
	curRes != none implies ride = none 
	ride != none implies curRes = none 
}

sig Minute{}

sig Reservation{
	code : one ReservationCode,
	user : one User,
	car : one Car,
	minutesLeft : set Minute
}{
	#minutesLeft < 60
	car.battery != ChargeNeeded
	car.doors = Locked
	car.motor = Off
}

sig Passenger{}

abstract sig RideStatus{}
sig RideCompleted, Riding extends RideStatus{}

sig Ride {
	code : one ReservationCode,
	status : one RideStatus,
	car : one Car,
	user : one User,
	ridingMinutes: some Minute,
	passengers: set Passenger,
	MSO : lone ChargingStation   // If MoneySavingOption is enabled it specified the chosen ChargingStation
}{
	#passengers <= #(car.seats) - 1
	MSO != none implies {
		one p : MSO.plugs | p.status = P_Reserved 
	}
}


abstract sig BillStatus{}
sig Paid, Rejected extends BillStatus{}

sig Bill{
	ride : one Ride,
	status : one BillStatus,
	amount : one Int
}{	

	(!getTenPercentDiscount[ride] and !getTwentyPercentDiscount[ride] and !getThirtyPercentDiscount[ride] and !getThirtyPercentMore[ride] and !getTwentyPercentDiscountMSO[ride]) implies amount = (mul[Company.costPerMinute, #(ride.ridingMinutes)])
	(getTenPercentDiscount[ride] and !getTwentyPercentDiscount[ride] and !getThirtyPercentDiscount[ride] and !getThirtyPercentMore[ride] and !getTwentyPercentDiscountMSO[ride]) implies amount = (mul[Company.costPerMinute, #(ride.ridingMinutes)]).applyDiscount[10]
	(!getTenPercentDiscount[ride] and getTwentyPercentDiscount[ride] and !getThirtyPercentDiscount[ride] and !getThirtyPercentMore[ride] and !getTwentyPercentDiscountMSO[ride]) implies amount = (mul[Company.costPerMinute, #(ride.ridingMinutes)]).applyDiscount[20]
	((!getTenPercentDiscount[ride] and !getTwentyPercentDiscount[ride] and getThirtyPercentDiscount[ride] and !getThirtyPercentMore[ride] and !getTwentyPercentDiscountMSO[ride]) or (getTenPercentDiscount[ride] and getTwentyPercentDiscount[ride] and !getThirtyPercentDiscount[ride] and !getThirtyPercentMore[ride] and !getTwentyPercentDiscountMSO[ride])) implies amount = (mul[Company.costPerMinute, #(ride.ridingMinutes)]).applyDiscount[30]
	(!getTenPercentDiscount[ride] and !getTwentyPercentDiscount[ride] and getThirtyPercentDiscount[ride] and !getThirtyPercentMore[ride] and !getTwentyPercentDiscountMSO[ride]) implies amount = (mul[Company.costPerMinute, #(ride.ridingMinutes)]).applyDiscount[40]
	(!getTenPercentDiscount[ride] and getTwentyPercentDiscount[ride] and getThirtyPercentDiscount[ride] and !getThirtyPercentMore[ride] and !getTwentyPercentDiscountMSO[ride]) implies amount = (mul[Company.costPerMinute, #(ride.ridingMinutes)]).applyDiscount[50]
	(getTenPercentDiscount[ride] and getTwentyPercentDiscount[ride] and getThirtyPercentDiscount[ride] and !getThirtyPercentMore[ride] and !getTwentyPercentDiscountMSO[ride]) implies amount = (mul[Company.costPerMinute, #(ride.ridingMinutes)]).applyDiscount[60]
	(!getTenPercentDiscount[ride] and !getTwentyPercentDiscount[ride] and !getThirtyPercentDiscount[ride] and getThirtyPercentMore[ride] and !getTwentyPercentDiscountMSO[ride]) implies amount = (mul[Company.costPerMinute, #(ride.ridingMinutes)]).applyDiscount[-30]
	(getTenPercentDiscount[ride] and !getTwentyPercentDiscount[ride] and !getThirtyPercentDiscount[ride] and getThirtyPercentMore[ride] and !getTwentyPercentDiscountMSO[ride]) implies amount = (mul[Company.costPerMinute, #(ride.ridingMinutes)]).applyDiscount[-20]
	(!getTenPercentDiscount[ride] and getTwentyPercentDiscount[ride] and !getThirtyPercentDiscount[ride] and getThirtyPercentMore[ride] and !getTwentyPercentDiscountMSO[ride]) implies amount = (mul[Company.costPerMinute, #(ride.ridingMinutes)]).applyDiscount[-10]
	(getTenPercentDiscount[ride] and !getTwentyPercentDiscount[ride] and !getThirtyPercentDiscount[ride] and !getThirtyPercentMore[ride] and getTwentyPercentDiscountMSO[ride]) implies amount = (mul[Company.costPerMinute, #(ride.ridingMinutes)]).applyDiscount[30]
	(!getTenPercentDiscount[ride] and getTwentyPercentDiscount[ride] and !getThirtyPercentDiscount[ride] and !getThirtyPercentMore[ride] and getTwentyPercentDiscountMSO[ride]) implies amount = (mul[Company.costPerMinute, #(ride.ridingMinutes)]).applyDiscount[40]
	(getTenPercentDiscount[ride] and getTwentyPercentDiscount[ride] and !getThirtyPercentDiscount[ride] and !getThirtyPercentMore[ride] and getTwentyPercentDiscountMSO[ride]) implies amount = (mul[Company.costPerMinute, #(ride.ridingMinutes)]).applyDiscount[50]
	(!getTenPercentDiscount[ride] and !getTwentyPercentDiscount[ride] and getThirtyPercentDiscount[ride] and !getThirtyPercentMore[ride] and getTwentyPercentDiscountMSO[ride]) implies amount = (mul[Company.costPerMinute, #(ride.ridingMinutes)]).applyDiscount[50]
	(getTenPercentDiscount[ride] and !getTwentyPercentDiscount[ride] and getThirtyPercentDiscount[ride] and !getThirtyPercentMore[ride] and getTwentyPercentDiscountMSO[ride]) implies amount = (mul[Company.costPerMinute, #(ride.ridingMinutes)]).applyDiscount[60]
	(!getTenPercentDiscount[ride] and getTwentyPercentDiscount[ride] and getThirtyPercentDiscount[ride] and !getThirtyPercentMore[ride] and getTwentyPercentDiscountMSO[ride]) implies amount = (mul[Company.costPerMinute, #(ride.ridingMinutes)]).applyDiscount[70]
	(getTenPercentDiscount[ride] and getTwentyPercentDiscount[ride] and getThirtyPercentDiscount[ride] and !getThirtyPercentMore[ride] and getTwentyPercentDiscountMSO[ride]) implies amount = (mul[Company.costPerMinute, #(ride.ridingMinutes)]).applyDiscount[80]
	
	ride.status = RideCompleted

}

//--------------------------------------------------------------- FACT -------------------------------------------------------

fact {
	all CS : CarStatus | CS in Car.status
}

fact {
	all BL : BatteryLevel |BL in Car.battery
}

fact {
	all r : ReservationCode | r in Reservation.code or r in Ride.code
}

fact {
	all b : BillStatus | b in Bill.status
}

fact {
	all p : Passenger | p in Ride.passengers
}

fact {
	all p : PlugStatus | p in Plug.status
}

fact {
	all ms : MotorStatus | ms in Car.motor
}

fact {
	all cd : CarDoors | cd in Car.doors
}

fact {
	all m : Minute | m in Ride.ridingMinutes or m in Reservation.minutesLeft
}

//--- USER ---

fact licenceNumberIsUnique {
	no disjoint u1, u2: User  |  u1.licenceNumber = u2.licenceNumber
}

//--- POSITION ---
fact eachPositionPairIsUnique{
	no disjoint p1,p2 : Position| p1.lat=p2.lat and p1.lon=p2.lon
}

//--- PLATE ---
fact eachPlateIsUnique{
	no disjoint c1, c2 : Car | c1.plate = c2.plate
}

fact noUnusedPlate{
	all p : Plate | one c : Car | p = c.plate 
}

//--- RESERVATION ---

fact reservationCodeIsUnique {
	no disjoint a, b : Reservation |  a.code = b.code
}

fact OneReservationPerUser{
	no disjoint r1, r2 : Reservation | r1.user = r2.user
}

fact OneCarPerReservation{
	no disjoint r1, r2 : Reservation | r1.car = r2.car
}

fact OnlyUsersBookCars{
	all r : Reservation | r.user in Company.users
}

fact {
	all u : User | u.curRes != none implies u.curRes.user = u
}

//--- RIDE ---

fact reservationCodeIsUnique2 {
	no disjoint r1, r2 : Ride |  r1.code = r2.code
}

fact OneRidePerUser{
	no disjoint r1, r2 : Ride | r1.user = r2.user
}

fact OneCarPerRide{
	no disjoint r1, r2 : Ride | r1.car = r2.car and r1.status = Riding and r2.status = Riding
}

fact OnlyUsersBookCars2{
	all r : Ride | r.user in Company.users
}

fact {
	all u : User | u.ride != none implies u.ride.user=u
}

//--- CHARGING STATION ---

fact chargingCarsAreInAStation{
	all c : Car |  c.status = Charging <=> c in ChargingStation.plugs.pluggedCar
}

fact carsArePluggedInOnlyOneStation {
	no cs1, cs2 : ChargingStation, c : Car | c=cs1.plugs.pluggedCar and c=cs2.plugs.pluggedCar
}

fact onlyLockedCarCanBeRecharged {
	no c : Car,  cs :  ChargingStation | c.doors = Unlocked and c in cs.plugs.pluggedCar
}

fact{
	all p : Plug | one cs : ChargingStation | p in cs.plugs
}

fact {
	all p : Plug | p in ChargingStation.plugs
}

fact{
	no p : Plug | p.status = P_InUse and p.pluggedCar= none
}

fact{
	all c : Car| one cs : ChargingStation | c.status = Charging implies c.pos in cs.area
}

//--- CAR ---

fact carAvailability{
	all c : Car | c.status = Available implies (c.battery != ChargeNeeded and c.doors = Locked and c.motor = Off)
}

fact carsUnlockedOnlyForARide{
	all c : Car| c.doors = Unlocked implies one r : Ride| r.car = c
}

//--- COMPANY ---

fact companyCars{
	all c : Car | c in Company.cars
}

fact {
	all cs :  ChargingStation  | cs in Company.stations
}

fact {
	all u :  User  | u in Company.users
}

fact {
	all p :  ParkingArea | p in Company.parkingAreas
}

//--- BILL ---

fact  noReservationOrRideUntillBillIsPaid{
	all u : User, b : Bill | ((u.curRes != none or u.ride != none) and b in u.bills) implies b.status = Paid
}

fact {
	all b : Bill | b in User.bills
}

fact {
	no disjoint u1, u2 : User | u1.bills & u2.bills != none
}

fact reservationCodeIsUnique3 {
	no disjoint b1, b2 : Bill |  b1.ride.code = b2.ride.code
}

//--- MISC

fact{
	all rs : RideStatus | rs in Ride.status
}

fact {
	all b : Bill, u: User | b in u.bills implies b.ride.user=u
}

fact {
	all r : Ride | one b : Bill | r. status = RideCompleted implies b.ride=r
}

fact {
	no disjoint c1, c2 : Car | c1.seats & c2.seats != none
}

fact{
	all c : Car | one p : Plug | ( c.status = Charging implies (p.pluggedCar = c and p.status= P_InUse))
}

fact {
	all l : Licence | l in User.licenceNumber
}

fact {
	all p : Plug | p.status = P_Reserved implies (one r : Ride | r.MSO != none and r.car.status = Reserved and r.status = Riding)
} 

//--------------------------------------------------------------- FUN ---------------------------------------------------------

fun Int.applyDiscount[discount : Int] : one Int{
	//	this-amount *discount	/100
	div[sub[this, mul[this, discount]],100]
}

fun Position.squaredDistance[p : Position]: one Int {
	mul[p.lat-this.lat, p.lat-this.lat]+mul[p.lon-this.lon,p.lon-this.lon]
}

// Returns the Position of the nearest Charging Station
fun nearestCS[p : Position] : one Position {
	{pCS : ChargingStation.area |
		all p2 :  ChargingStation.area | pCS.squaredDistance[p] <= p2.squaredDistance[p]
	}
}

//--------------------------------------------------------------- PRED -------------------------------------------------------

pred getTenPercentDiscount[r : Ride]{
	(#r.passengers) >= 2
}

pred getTwentyPercentDiscount[r : Ride]{
	r.car.battery = MoreThanHalf
}

pred getThirtyPercentDiscount[r : Ride]{
	r.car.status = Charging
}

pred getThirtyPercentMore[r : Ride]{
	r.car.battery = ChargeNeeded or  nearestCS[r.car.pos].squaredDistance[r.car.pos] > 9000000
}

pred getTwentyPercentDiscountMSO[r : Ride]{
	r.MSO != none and r.car.pos in r.MSO.area and r.car in r.MSO.plugs.pluggedCar
}


pred show(){
	/*#(Company.cars) >1
	#(Company.users) >1
	#(Riding) >1
	#(Company.stations) > 1
	#(Company.parkingAreas) > 1
	//#(P_InUse) = 0
	#(P_Available) > 0
	#(P_Reserved) > 0*/
	#(Plug.pluggedCar) > 1
	

}


run show for 4


