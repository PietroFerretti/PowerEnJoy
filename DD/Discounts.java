package powerEnJoy;

import java.util.List;

import graphHopper.GraphHopper;

public class Discounts
{
	private List<PowerGridStation> pgsList;
	private final static int MAXDISTANCE = 3000;
	
	public int calculatesDiscount(int amount, Car car, Ride ride)
	{
		int minDistance = 1000000000;
		int distance = 0;
		for(PowerGridStation pgs : pgsList)
		{
			distance = GraphHopper.distance(pgs.getPosition(), car.getPosition());
			if(distance < minDistance)
				minDistance = distance;
		}
			  
		
		int discountPercentage = 0;
		
		if(car.getPassengers() > 1)
			discountPercentage += 10;
		if(car.getBattery() > 50)
			discountPercentage += 20;
		if(car.isCharging())
			discountPercentage += 30;
		if(car.getBattery() < 20 || minDistance > MAXDISTANCE)
			discountPercentage -= 30;
		if(ride.isMso() && (ride.getChosenPGS().getPosition().equals(car.getPosition())))
			discountPercentage += 10;
		
		int discount = amount * (discountPercentage/100);
		
		return (amount - discount);
	}
}
