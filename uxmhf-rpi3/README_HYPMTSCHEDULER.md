# Micro-hypervisor based Mixed Trust Scheduler uberapp

## Instructions to build and run kernel-mode test application for mixed-trust scheduler

1.  Follow all instructions described in README.md and stop after 
building `uhcalltest` on development system

1. At this point build `hypmtschedulertestkmod.ko` on development system
	1. `cd rgapps/linux/ugapp-hypmtscheduler-zsrmv`
	1. `./build.sh ~/linux ~/tools/arm-bcm2708/gcc-linaro-arm-linux-gnueabihf-raspbian-x64/bin/`
	1. `cp ./hypmtschedulertestkmod.ko ~/uxmhf-rpi3-staging/.`

1. Build `hypmtschedulertest_userapp` on development system
	1. `cd rgapps/linux/ugapp-hypmtscheduler-zsrmv`
	1. `make builduserapp`
	1. `cp ./hypmtschedulertest_userapp.ko ~/uxmhf-rpi3-staging/.`

1. Continue with remaining instructions described in README.md and boot the
micro-hypervisor with the uberguest

1. Install `hypmtschedulertestkmod.ko` within uberguest
	1. `sudo insmod hypmtschedulertestkmod.ko`

1. Run `hypmtschedulertest_userapp` (hypmtscheduler user-mode test application) within uberguest to create a hyptask
	1. `sudo ./hypmtschedulertest_userapp 1`

1. Run `hypmtschedulertest_userapp` (hypmtscheduler user-mode test application) within uberguest to disable hyptask execution for a period
	1. `sudo ./hypmtschedulertest_userapp 2`

1. Run `hypmtschedulertest_userapp` (hypmtscheduler user-mode test application) within uberguest to delete hyptask
	1. `sudo ./hypmtschedulertest_userapp 3`


1. Note: `disable` and `delete` only work on the first hyptask created for the above example. However, it is straightforward to modify the kernel module and the user-mode application to support multiple hyptasks as required



## Instructions to build and run user-mode test application for mixed-trust scheduler

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

