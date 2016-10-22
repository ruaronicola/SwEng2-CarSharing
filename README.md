# Software Engineering 2: PowerEnjoy


![Image not found](resources/images/powerEnjoy.png)
<sub>*Shared project by Giacomo Gregori and Nicola Ruaro*</sub>


### Problem Description

You are to develop a digital management system for a car-sharing service that exclusively employs electric cars. First, the system should provide the functionality normally provided by car-sharing services. These include:

* Users must be able to register to the system by providing their credentials and payment information. They receive back a password that can be used to access the system.
* Registered users must be able to find the locations of available cars within a certain distance from their current location or from a specified address.
* Among the available cars in a certain geographical region, users must be able to reserve a single car for up to one hour before they pick it up.
* If a car is not picked-up within one hour from the reservation, the system tags the car as available again, and the reservation expires; the user pays a fee of 1 EUR.
* A user that reaches a reserved car must be able to tell the system she’s nearby, so the system unlocks the car and the user may enter.
* As soon as the engine ignites, the system starts charging the user for a given amount of money per minute; the user is notified of the current charges through a screen on the car.
* The system stops charging the user as soon as the car is parked in a safe area and the user exits the car; at this point, the system locks the car automatically.
* The set of safe areas for parking cars is pre-defined by the management system.

In addition to the functionality above, the system should incentivize the virtuous behaviors of the
users. Specifically:

1.  If the system detects the user took at least two other passengers onto the car, the system applies a discount of 10% on the last ride.
2.  If a car is left with no more than 50% of the battery empty, the system applies a discount of 20% on the last ride.
3.  If a car is left at special parking areas where they can be recharged and the user takes care of plugging the car into the power grid, the system applies a discount of 30% on the last ride.
4.  If a car is left at more than 3 KM from the nearest power grid station or with more than 80% of the battery empty, the system charges 30% more on the last ride to compensate for the cost required to re-charge the car on-site.


### Deadlines

* **Group registration** deadline: 16/10/2016
* **[RASD](https://github.com/ruaronicola/SwEng2-CarSharing/files/545467/RASD.pdf)** submission deadline: 13/11/2016
* **DD** submission deadline: 11/12/2016
* **Testing document** submission deadline: 15/01/2017
* **Project management** deadline: 22/01/2017
* **Code inspection** deadline: 05/02/2017
* **Final presentation**: (to be scheduled)
