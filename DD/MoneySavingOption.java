package powerEnJoy;

import graphHopper.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

public class MoneySavingOption
{
	private final static int TIMEDISTANCE = 300;  	//300 seconds = 5 minutes
	private final static int SPACEDISTANCE = 500;	//500 metres
	
	private List<PowerGridStation> pgsList;
	private List<Car> availableCar;
	
	public PowerGridStation moneySavingOption(String address)
	{
		Map<PowerGridStation, Integer> count = new HashMap<>();
		GeoPosition destination = GraphHopper.geocoding(address);
		List<PowerGridStation> accettablepgs = new ArrayList<>();
		
		//looks for the power grid stations reachable in a reasonable time
		for(PowerGridStation pgs : pgsList)
			if(GraphHopper.isochrone(destination, pgs.getPosition()) < TIMEDISTANCE)
				accettablepgs.add(pgs);
		
		//estimates the "density" of the cars near a power grid station
		for(PowerGridStation pgs : accettablepgs)
		{
			int i = 0;
			
			for(Car car : availableCar)
				if(GraphHopper.distance(car.getPosition(), pgs.getPosition()) < SPACEDISTANCE)
					i++;
			
			count.put(pgs, i);
		}
			
		PowerGridStation chosenPGS = null;
		int min = 1000000000;
		
		//finds the power grid station with the minimum "density"
		for(Entry<PowerGridStation, Integer> entry : count.entrySet())
			if(entry.getValue() < min)
				chosenPGS = entry.getKey();
			
		return chosenPGS;
	}
}
