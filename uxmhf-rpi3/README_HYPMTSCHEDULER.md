# Micro-hypervisor based Mixed Trust Scheduler uberapp

1.  Follow all instructions described in README.md and stop after 
building `uhcalltest` on development system

1. At this point build `ugapp-hypmtscheduler` on development system
	1. `cd rgapps/linux`
	1. `make -w all`
	1. `cd ugapp-hypmtscheduler`
	1. `make -w all`
	1. `cp ./ugapp-hypmtschedulert ~/uxmhf-rpi3-staging/.`

1. Continue with remaining instructions described in README.md and boot the
micro-hypervisor with the uberguest

1. Install `uhcallkmod` within uberguest
	1. `sudo insmod uhcallkmod`

1. Run `ugapp-hypmtscheduler` (hypmtscheduler user-mode test application) within uberguest
	1. `sudo ./ugapp-hypmtschedulertest`

1. Remove `uhcallkmod` within uberguest once done
	1. `sudo rmmod uhcallkmod`

1. Shutdown the uberguest
	1. `sudo shutdown -hP now`

