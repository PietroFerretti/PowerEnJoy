/*TODO
1. We assume there is at least one safe area. DA INSERIRE NEL RASD DA QUALCHE PARTE?
2. CHECK ma la macchina posso lasciarla solo nelle safe areas?
3. CHECK il numero di plugs deve essere almeno 1?
4. chargingstation pluggedcars fact
5. noInstance se metto some invece che set in company
6. gestire sig Used, TemporaryBreak
7. FACT EachReservationHasCorrespondingUser, mi serve?
8. MSO implies reserved Plug
9. quando parcheggio (sia lì che da un'altra parte) tolgo il reserved + aggiungere facts
10. controllare che chargeneeded non può esssere prenotata
*/

open util/integer as integer

//--------------------------------------------------------------- SIG --------------------------------------------------------

//Geographical position (simplified in this model using pair of Int instead of Float)
sig Position{
	lat: one Int,
	lon: one Int
}

//Container of all positions recognized by our system
one sig Map{
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
one sig P_Reserved, P_Available extends PlugStatus{} //reserved if user has a MSO enabled

sig Plug{
	status : PlugStatus
}{
	status = P_Reserved implies one r : Ride | r.MSO != none and r.car.status = Reserved
}

/*
We assume a charging station is in our model (system?) if it has at least one working plug
(either available or not). 
*/
sig ChargingStation extends SafeArea{
	plugs : some Plug, 
	pluggedCars: set Car
}{
	//#plugs > 0 risolto con some invece di set
	#(pluggedCars)<=#(plugs)
	all c : Car | c in pluggedCars implies c.pos in area
	//plugstatus??
}

sig Plate{}
sig Seat{}
abstract sig CarStatus{}
sig Available, Charging, Reserved extends CarStatus{}
sig Used, TemporaryBreak extends Reserved{}//serve?
abstract sig BatteryLevel{}
sig MoreThanHalf, ChargeNeeded,  /*<=20%*/ OtherBatteryLevel extends BatteryLevel{} //COME LE GESTIAMO??
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
	//TODO
}{
	// anche no? SONO DIVENTATI SEATS #passengers <= 4 //We assume 5 seats in each car
	#seats >= 2
	(doors = Locked or status = Charging or status = TemporaryBreak /*anche il break??*/  ) implies motor = Off
	(status = Charging or status = Available) implies doors = Locked
	status = Available implies pos in SafeArea.area
	motor = On implies doors = Unlocked
}

/*
set of all electric cars, areas, station
*/
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
//TODO suspeded
sig User{//estendo con registered user?
	licenceNumber : one Licence, //mai usato però
	curPos : one Position, //o lone
	curRes : lone Reservation, //FACT no reservation se sta usando una macchina //CHECK forse basta il fatto che sia lone
	ride : lone Ride,
	bills : set Bill
	//TO DO providing credentials and payment infos
} {
	curRes != none implies ride = none //?? ha senso?
	ride != none implies curRes = none //non posso prenotare mentre sto già usando una macchina
//una carta per user? forse meglio di no 
//They receive back a password that can be used to access the system PW È UNICA FACT(ma no, cazzata)
}

sig Minute{}

sig Reservation{
	code : one ReservationCode,
	user : one User,
	car : one Car,
	minutesLeft : set Minute
}{
	#minutesLeft < 60
//forse superflue mettere in reserved?
	car.battery != ChargeNeeded
	car.doors = Locked
	car.motor = Off
	//contraint su user?
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
	MSO : lone ChargingStation //If MoneySavingOption is enabled it specified the chosen ChargingStation
}{
	#passengers <= #(car.seats) - 1
	MSO != none implies {
		one p : MSO.plugs | p.status = P_Reserved 
	}
}


abstract sig BillStatus{}
sig Oustanding, Paid, Rejected extends BillStatus{}

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




fun Int.applyDiscount[discount : Int] : one Int{
//	this-amount*discount	/100
	div[sub[this, mul[this, discount]],100]
}

//--------------------------------------------------------------- FACT -------------------------------------------------------

fact {
	all CS : CarStatus | one c : Car | CS = c.status
}

fact {
	all BL : BatteryLevel | one c : Car | BL = c.battery
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

fact noUnusedPlate{//serve??
	all p : Plate | one c : Car | p = c.plate //Car.plate = Plate(OSIO)
}

//--- RESERVATION ---

fact reservationCodeIsUnique {
	no disjoint a, b : Reservation |  a.code = b.code
}

//FACT no 2 user per car
fact OneReservationPerUser{
	no disjoint r1, r2 : Reservation | r1.user = r2.user
}

//FACT no 2 reservation per CAR
fact OneCarPerReservation{
	no disjoint r1, r2 : Reservation | r1.car = r2.car
}

//faccio prenotazione solo se sono un user
fact OnlyUsersBookCars{
	all r : Reservation | r.user in Company.users
}

fact /*?????*/ {
	all u : User | u.curRes != none implies u.curRes.user = u
}//pure bill e ride

//--- RIDE ---

fact reservationCodeIsUnique2 {
	no disjoint r1, r2 : Ride |  r1.code = r2.code
}

//FACT no 2 user per car
fact OneRidePerUser{
	no disjoint r1, r2 : Ride | r1.user = r2.user
}

//FACT no 2 ride per CAR
fact OneCarPerRide{
	no disjoint r1, r2 : Ride | r1.car = r2.car
}

//faccio prenotazione solo se sono un user
fact OnlyUsersBookCars2{
	all r : Ride | r.user in Company.users
}


fact /*?????*/ {
	all u : User | u.ride != none implies u.ride.user=u
}

//--- CHARGING STATION ---
fact eachChargingCarBelongsToOneStation{
	all c : Car | one cs :  ChargingStation  | c.status = Charging <=> c in cs.pluggedCars
}

fact onlyLockedCarCanBeRecharged {//superflua??
	no c : Car,  cs :  ChargingStation | c.doors = Unlocked and c in cs.pluggedCars
}

fact eachPlugBelongsToOneStation{
	no cs1, cs2 : ChargingStation | cs1.plugs & cs2.plugs != none
}

fact {
	all p : Plug | p in ChargingStation.plugs
}

//--- CAR ---
fact carAvailability{
	all c : Car | c.status = Available implies (c.battery != ChargeNeeded and c.doors = Locked and c.motor = Off)
}

fact unlockedCarsHaveARideAssociated {//cambiare nome(OSIO)
	all c : Car| c.doors = Unlocked implies one r : Ride| r.car = c
}

//--- COMPANY ---

//all cars have to belong to the company
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
fact {
	all l : Licence | l in User.licenceNumber
}

//--------------------------------------------------------------- PRED -------------------------------------------------------

pred getTenPercentDiscount[r : Ride]{
	(#r.passengers) >= 2
}

pred getTwentyPercentDiscount[r : Ride]{
	r.car.battery = MoreThanHalf
}

pred getThirtyPercentDiscount[r : Ride]{
	r.car.status = Charging //dovrebbe bastare essendoci un fact
}

pred getThirtyPercentMore[r : Ride]{
//CHECK
	r.car.battery = ChargeNeeded or  nearestCS[r.car.pos].squaredDistance[r.car.pos] > 9000000
}

pred getTwentyPercentDiscountMSO[r : Ride]{
	r.MSO != none and r.car.pos in r.MSO.area and r.car in r.MSO.pluggedCars
}


//TODO problema tra parkingareas e car , parking areas e user, stations
pred show(){
	#(Company.cars) >1
	#(Company.users) >1
	#(Riding) >1

 //	#(Company.stations) > 1
  #(Company.parkingAreas) > 0
}

//--------------------------------------------------------------- FUN ---------------------------------------------------------

//--- POSITION ---
fun Position.squaredDistance[p : Position]: one Int {
	mul[p.lat-this.lat, p.lat-this.lat]+mul[p.lon-this.lon,p.lon-this.lon]
}

//It returns the Position of the nearest Charging Station
fun nearestCS[p : Position] : one Position {
	{pCS : ChargingStation.area |
		all p2 :  ChargingStation.area | pCS.squaredDistance[p] <= p2.squaredDistance[p]
	}
}


run show for 4


