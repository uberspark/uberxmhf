# Micro-hypervisor based MAVLINK serial heart-beat (mavlinkserhb) uberapp

## Instructions to build and run mavlinkserhb

1.  Follow all instructions described in README.md and stop after 
building `uhcalltest` on development system

1. At this point build `mavlinkserhbkmod.ko` on development system
	1. `cd rgapps/linux/ugapp-mavlinkserhb`
	1. `make -C ~/linux ARCH=arm CROSS_COMPILE=~/tools/arm-bcm2708/gcc-linaro-arm-linux-gnueabihf-raspbian-x64/bin/arm-linux-gnueabihf- M=$PWD`
	1. `cp ./mavlinkserhbkmod.ko ~/uxmhf-rpi3-staging/.`

1. Build `mavlinkserhb_userapp` on development system
	1. `cd rgapps/linux/ugapp-mavlinkserhb`
	1. `make builduserapp`
	1. `cp ./mavlinkserhb_userapp.ko ~/uxmhf-rpi3-staging/.`

1. Continue with remaining instructions described in README.md and boot the
micro-hypervisor with the uberguest

1. Install `mavlinkserhbkmod.ko` within uberguest
	1. `sudo insmod mavlinkserhbkmod.ko`

1. Run `mavlinkserhb_userapp` (mavlinkserhb user-mode test application) within uberguest to start heart-beat protocol
	1. `sudo ./mavlinkserhb_userapp 1`

## Developer notes for mavlinkserhb

1. mavlinkserhb is controlled via a user-space application that interacts with the mavlinkserhb kernel module(`ugapp-mavlinkserhbkmod`), which in turn interacts with the mavlinkserhb hyptask uberapp(`uapp-mavlinkserhb`). 


1. The default periodic heart-beat protocol relies on a serial loopback interface and sends a 8-byte buffer followed by a read which expects the same 8-byte buffer sent. The system is halted if the received buffer does not match the send bufer.


1. The heart-beat protocol can be customized within the function `` in `` 

The following kernel-mode module APIs are available to bridge the hypervisor scheduler APIs (defined within `rgapps/linux/ugapp-hypmtscheduler-zsrmv\hypmtscheduler_kmodlib.c`)
	1.  `bool hypmtscheduler_createhyptask(u32 first_period, u32 regular_period,
			u32 priority, u32 hyptask_id, u32 *hyptask_handle)`
		1. creates a hyptask with specified `first_period`, `regular_period` and `priority`
		1. `first_period` and `regular_period` are hyptask time-periods specified as clock-cycles. For convenience definitions `HYPMTSCHEDULER_TIME_1SEC`, `HYPMTSCHEDULER_TIME_1MSEC` and `HYPMTSCHEDULER_TIME_1USEC` are provided within `include/hypmtscheduler.h` for approx. clock-cycles corresponding to 1 second, milli-second and micro-second respectively.
		1. `priority` is a `u32` with higher number indicating higher priority
		1. `hyptask_id` is a number from 0 to `HYPMTSCHEDULER_MAX_HYPTASKID` (defined within `include/hypmtscheduler.h`) which selects a hyptask function to execute
		1. hyptask functions are defined within `uapps/uapp-hypmtscheduler/uapp-hypmtscheduler.c` and mapped via the array `HYPTHREADFUNC hyptask_idlist`	
		1. `hyptask_handle` contains the hyptask reference upon successful hyptask creation (i.e., when the function `hypmtscheduler_createhyptask` returns `true`)
	1.  `bool hypmtscheduler_disablehyptask(u32 hyptask_handle)`
		1. disables hyptask execution for a hyptask referenced by `hyptask_handle`
		1. `hyptask_handle` is the reference of the hyptask returned by a previous invocation to `hypmtscheduler_createhyptask`
		1. returns `true` on success
	1.  `bool hypmtscheduler_deletehyptask(u32 hyptask_handle)`
		1. deletes a hyptask for a hyptask referenced by `hyptask_handle`
		1. `hyptask_handle` is the reference of the hyptask returned by a previous invocation to `hypmtscheduler_createhyptask`
		1. returns `true` on success
	1.  `bool hypmtscheduler_getrawtick32(u32 *tickcount)`
		1. gets 32-bit raw time-stamp counter value for CPU
		1. returns `true` on success
	1.  `bool hypmtscheduler_getrawtick64(u64 *tickcount)`
		1. gets 64-bit raw time-stamp counter value for CPU
		1. returns `true` on success
		

1. You will need to include `rgapps/linux/ugapp-hypmtscheduler-zsrmv\hypmtscheduler_kmodlib.c` and `include/hypmtscheduler.h` within your own custom kernel module build in the event you want to use the hyper scheduler APIs within your own kernel-module. See `rgapps/linux/ugapp-hypmtscheduler-zsrmv\Makefile` for further details.


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

