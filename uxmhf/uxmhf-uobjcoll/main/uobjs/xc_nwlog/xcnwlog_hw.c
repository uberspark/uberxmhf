/*
 * @XMHF_LICENSE_HEADER_START@
 *
 * eXtensible, Modular Hypervisor Framework (XMHF)
 * Copyright (c) 2009-2012 Carnegie Mellon University
 * Copyright (c) 2010-2012 VDG Inc.
 * All Rights Reserved.
 *
 * Developed by: XMHF Team
 *               Carnegie Mellon University / CyLab
 *               VDG Inc.
 *               http://xmhf.org
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in
 * the documentation and/or other materials provided with the
 * distribution.
 *
 * Neither the names of Carnegie Mellon or VDG Inc, nor the names of
 * its contributors may be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND
 * CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED
 * TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
 * TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
 * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * @XMHF_LICENSE_HEADER_END@
 */

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-hwm.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xc.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xc_nwlog.h>

/*
 * slab code
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */


//////
// e1000e hardware related support functions
//////


static void e1000_clear_vfta(struct e1000_hw *hw);
static int32_t e1000_get_auto_rd_done(struct e1000_hw *hw);
static int32_t e1000_get_hw_eeprom_semaphore(struct e1000_hw *hw);
static int32_t e1000_get_phy_cfg_done(struct e1000_hw *hw);
static void e1000_init_rx_addrs(struct e1000_hw *hw);
static void e1000_initialize_hardware_bits(struct e1000_hw *hw);
static void e1000_put_hw_eeprom_semaphore(struct e1000_hw *hw);
static int32_t e1000_set_d0_lplu_state(struct e1000_hw *hw, bool active);
static void e1000_set_pci_express_master_disable(struct e1000_hw *hw);
static int32_t e1000_setup_copper_link(struct e1000_hw *hw);
static int32_t e1000_spi_eeprom_ready(struct e1000_hw *hw);
static void e1000_raise_ee_clk(struct e1000_hw *hw, uint32_t *eecd);
static void e1000_lower_ee_clk(struct e1000_hw *hw, uint32_t *eecd);
static void e1000_shift_out_ee_bits(struct e1000_hw *hw, uint16_t data,
                                    uint16_t count);
static int32_t e1000_write_phy_reg_ex(struct e1000_hw *hw, uint32_t reg_addr,
                                      uint16_t phy_data);
static int32_t e1000_read_phy_reg_ex(struct e1000_hw *hw,uint32_t reg_addr,
                                     uint16_t *phy_data);
static uint16_t e1000_shift_in_ee_bits(struct e1000_hw *hw, uint16_t count);
static int32_t e1000_acquire_eeprom(struct e1000_hw *hw);
static void e1000_release_eeprom(struct e1000_hw *hw);
static void e1000_standby_eeprom(struct e1000_hw *hw);

void e1000_delay(uint64_t count)
{
	if (count)
		while (count --);
}

/******************************************************************************
 * Reset the transmit and receive units; mask and clear all interrupts.
 *
 * hw - Struct containing variables accessed by shared code
 *****************************************************************************/
int32_t
e1000_reset_hw(struct e1000_hw *hw)
{
    uint32_t ctrl;
    uint32_t icr;
    int32_t ret_val;

    DEBUGFUNC("e1000_reset_hw");

    {
        /* Prevent the PCI-E bus from sticking if there is no TLP connection
         * on the last TLP read/write transaction when MAC is reset.
         */
        if (e1000_disable_pciex_master(hw) != E1000_SUCCESS) {
            DEBUGOUT("PCI-E Master disable polling has failed.\n");
        }
    }

    /* Clear interrupt mask to stop board from generating interrupts */
    DEBUGOUT("Masking off all interrupts\n");
    E1000_WRITE_REG(hw, IMC, 0xffffffff);

    /* Disable the Transmit and Receive units.  Then delay to allow
     * any pending transactions to complete before we hit the MAC with
     * the global reset.
     */
    E1000_WRITE_REG(hw, RCTL, 0);
    E1000_WRITE_REG(hw, TCTL, E1000_TCTL_PSP);
    E1000_WRITE_FLUSH(hw);

    /* Delay to allow any outstanding PCI transactions to complete before
     * resetting the device
     */
    e1000_msleep(10);

    ctrl = E1000_READ_REG(hw, CTRL);

    /* Issue a global reset to the MAC.  This will reset the chip's
     * transmit, receive, DMA, and link units.  It will not effect
     * the current PCI configuration.  The global reset bit is self-
     * clearing, and should clear within a microsecond.
     */
    DEBUGOUT("Issuing a global reset to MAC\n");
    E1000_WRITE_REG(hw, CTRL, (ctrl | E1000_CTRL_RST));

    /* After MAC reset, force reload of EEPROM to restore power-on settings to
     * device.  Later controllers reload the EEPROM automatically, so just wait
     * for reload to complete.
     */
    {
            /* Auto read done will delay 5ms or poll based on mac type */
            ret_val = e1000_get_auto_rd_done(hw);
            if (ret_val)
                return ret_val;
    }

    /* Clear interrupt mask to stop board from generating interrupts */
    DEBUGOUT("Masking off all interrupts\n");
    E1000_WRITE_REG(hw, IMC, 0xffffffff);

    /* Clear any pending interrupt events. */
    icr = E1000_READ_REG(hw, ICR);

    return E1000_SUCCESS;
}

/******************************************************************************
 *
 * Initialize a number of hardware-dependent bits
 *
 * hw: Struct containing variables accessed by shared code
 *
 * This function contains hardware limitation workarounds for PCI-E adapters
 *
 *****************************************************************************/
static void
e1000_initialize_hardware_bits(struct e1000_hw *hw)
{
    {
        /* Settings common to all PCI-express silicon */
        uint32_t reg_tarc0, reg_tarc1;
        uint32_t reg_tctl;
        uint32_t reg_txdctl, reg_txdctl1;

        /* link autonegotiation/sync workarounds */
        reg_tarc0 = E1000_READ_REG(hw, TARC0);
        reg_tarc0 &= ~((1 << 30)|(1 << 29)|(1 << 28)|(1 << 27));

        /* Enable not-done TX descriptor counting */
        reg_txdctl = E1000_READ_REG(hw, TXDCTL);
        reg_txdctl |= E1000_TXDCTL_COUNT_DESC;
        E1000_WRITE_REG(hw, TXDCTL, reg_txdctl);
        reg_txdctl1 = E1000_READ_REG(hw, TXDCTL1);
        reg_txdctl1 |= E1000_TXDCTL_COUNT_DESC;
        E1000_WRITE_REG(hw, TXDCTL1, reg_txdctl1);

        {
                /* Clear PHY TX compatible mode bits */
                reg_tarc1 = E1000_READ_REG(hw, TARC1);
                reg_tarc1 &= ~((1 << 30)|(1 << 29));

                /* link autonegotiation/sync workarounds */
                reg_tarc0 |= ((1 << 26)|(1 << 25)|(1 << 24)|(1 << 23));

                /* TX ring control fixes */
                reg_tarc1 |= ((1 << 26)|(1 << 25)|(1 << 24));

                /* Multiple read bit is reversed polarity */
                reg_tctl = E1000_READ_REG(hw, TCTL);
                if (reg_tctl & E1000_TCTL_MULR)
                    reg_tarc1 &= ~(1 << 28);
                else
                    reg_tarc1 |= (1 << 28);

                E1000_WRITE_REG(hw, TARC1, reg_tarc1);
        }

        E1000_WRITE_REG(hw, TARC0, reg_tarc0);
    }
}

/******************************************************************************
 * Performs basic configuration of the adapter.
 *
 * hw - Struct containing variables accessed by shared code
 *
 * Assumes that the controller has previously been reset and is in a
 * post-reset uninitialized state. Initializes the receive address registers,
 * multicast table, and VLAN filter table. Calls routines to setup link
 * configuration and flow control settings. Clears all on-chip counters. Leaves
 * the transmit and receive units disabled and uninitialized.
 *****************************************************************************/
int32_t
e1000_init_hw(struct e1000_hw *hw)
{
    uint32_t ctrl;
    uint32_t i;
    int32_t ret_val;
    uint32_t mta_size;

    DEBUGFUNC("e1000_init_hw");

    /* Must be called after e1000_set_media_type because media_type is used */
    e1000_initialize_hardware_bits(hw);

    /* Disabling VLAN filtering. */
    DEBUGOUT("Initializing the IEEE VLAN\n");
    /* VET hardcoded to standard value and VFTA removed in ICH8 LAN */
    {
        e1000_clear_vfta(hw);
    }

    /* Setup the receive address. This involves initializing all of the Receive
     * Address Registers (RARs 0 - 15).
     */
    e1000_init_rx_addrs(hw);

    /* Zero out the Multicast HASH table */
    DEBUGOUT("Zeroing the MTA\n");
    mta_size = E1000_MC_TBL_SIZE;
    for (i = 0; i < mta_size; i++) {
        E1000_WRITE_REG_ARRAY(hw, MTA, i, 0);
        /* use write flush to prevent Memory Write Block (MWB) from
         * occuring when accessing our register space */
        E1000_WRITE_FLUSH(hw);
    }

    /* Call a subroutine to configure the link and setup flow control. */
    ret_val = e1000_setup_link(hw);

    /* Set the transmit descriptor write-back policy */
    {
        ctrl = E1000_READ_REG(hw, TXDCTL);
        ctrl = (ctrl & ~E1000_TXDCTL_WTHRESH) | E1000_TXDCTL_FULL_TX_DESC_WB;
        E1000_WRITE_REG(hw, TXDCTL, ctrl);
    }

    {
        ctrl = E1000_READ_REG(hw, TXDCTL1);
        ctrl = (ctrl & ~E1000_TXDCTL_WTHRESH) | E1000_TXDCTL_FULL_TX_DESC_WB;
        E1000_WRITE_REG(hw, TXDCTL1, ctrl);
    }

    return ret_val;
}

/******************************************************************************
 * Configures flow control and link settings.
 *
 * hw - Struct containing variables accessed by shared code
 *
 * Determines which flow control settings to use. Calls the apropriate media-
 * specific link configuration function. Configures the flow control settings.
 * Assuming the adapter has a valid link partner, a valid link should be
 * established. Assumes the hardware has previously been reset and the
 * transmitter and receiver are not enabled.
 *****************************************************************************/
int32_t
e1000_setup_link(struct e1000_hw *hw)
{
    int32_t ret_val;

    DEBUGFUNC("e1000_setup_link");

    /* In the case of the phy reset being blocked, we already have a link.
     * We do not have to set it up again. */
    if (e1000_check_phy_reset_block(hw))
        return E1000_SUCCESS;

    /* Call the necessary subroutine to configure the link. */
    ret_val = e1000_setup_copper_link(hw);

    /* Initialize the flow control address, type, and PAUSE timer
     * registers to their default values.  This is done even if flow
     * control is disabled, because it does not hurt anything to
     * initialize these registers.
     */
    DEBUGOUT("Initializing the Flow Control address, type and timer regs\n");

    /* FCAL/H and FCT are hardcoded to standard values in e1000_ich8lan. */
    {
        E1000_WRITE_REG(hw, FCT, FLOW_CONTROL_TYPE);
        E1000_WRITE_REG(hw, FCAH, FLOW_CONTROL_ADDRESS_HIGH);
        E1000_WRITE_REG(hw, FCAL, FLOW_CONTROL_ADDRESS_LOW);
    }

    E1000_WRITE_REG(hw, FCTTV, hw->fc_pause_time);

    /* Set the flow control receive threshold registers.  Normally,
     * these registers will be set to a default threshold that may be
     * adjusted later by the driver's runtime code.  However, if the
     * ability to transmit pause frames in not enabled, then these
     * registers will be set to 0.
     */
    {
        E1000_WRITE_REG(hw, FCRTL, 0);
        E1000_WRITE_REG(hw, FCRTH, 0);
    }
    return ret_val;
}

/******************************************************************************
* Make sure we have a valid PHY and change PHY mode before link setup.
*
* hw - Struct containing variables accessed by shared code
******************************************************************************/
static int32_t
e1000_copper_link_preconfig(struct e1000_hw *hw)
{
    uint32_t ctrl;

    DEBUGFUNC("e1000_copper_link_preconfig");

    ctrl = E1000_READ_REG(hw, CTRL);
    /* With 82543, we need to force speed and duplex on the MAC equal to what
     * the PHY speed and duplex configuration is. In addition, we need to
     * perform a hardware reset on the PHY to take it out of reset.
     */
    {
        ctrl |= E1000_CTRL_SLU;
        ctrl &= ~(E1000_CTRL_FRCSPD | E1000_CTRL_FRCDPX);
        E1000_WRITE_REG(hw, CTRL, ctrl);
    }

   return E1000_SUCCESS;
}


/********************************************************************
* Copper link setup for e1000_phy_igp series.
*
* hw - Struct containing variables accessed by shared code
*********************************************************************/
static int32_t
e1000_copper_link_igp_setup(struct e1000_hw *hw)
{
    int32_t ret_val;
    uint16_t phy_data;

    DEBUGFUNC("e1000_copper_link_igp_setup");

    ret_val = e1000_phy_reset(hw);
    if (ret_val) {
        DEBUGOUT("Error Resetting the PHY\n");
        return ret_val;
    }

    /* Wait 15ms for MAC to configure PHY from eeprom settings */
    e1000_msleep(15);
    /* disable lplu d0 during driver init */
    ret_val = e1000_set_d0_lplu_state(hw, false);
    if (ret_val) {
        DEBUGOUT("Error Disabling LPLU D0\n");
        return ret_val;
    }
    /* Configure mdi-mdix settings */
    ret_val = e1000_read_phy_reg(hw, IGP01E1000_PHY_PORT_CTRL, &phy_data);
    if (ret_val)
        return ret_val;

    {
        phy_data &= ~IGP01E1000_PSCR_AUTO_MDIX;
        phy_data |= IGP01E1000_PSCR_AUTO_MDIX;
    }
    ret_val = e1000_write_phy_reg(hw, IGP01E1000_PHY_PORT_CTRL, phy_data);
    if (ret_val)
        return ret_val;

    return E1000_SUCCESS;
}

/********************************************************************
* Setup auto-negotiation and flow control advertisements,
* and then perform auto-negotiation.
*
* hw - Struct containing variables accessed by shared code
*********************************************************************/
static int32_t
e1000_copper_link_autoneg(struct e1000_hw *hw)
{
    int32_t ret_val;
    uint16_t phy_data;

    DEBUGFUNC("e1000_copper_link_autoneg");

    /* If autoneg_advertised is zero, we assume it was not defaulted
     * by the calling code so we set to advertise full capability.
     */

    hw->autoneg_advertised = AUTONEG_ADVERTISE_SPEED_DEFAULT;

    DEBUGOUT("Reconfiguring auto-neg advertisement params\n");
    ret_val = e1000_phy_setup_autoneg(hw);
    if (ret_val) {
        DEBUGOUT("Error Setting up Auto-Negotiation\n");
        return ret_val;
    }
    DEBUGOUT("Restarting Auto-Neg\n");

    /* Restart auto-negotiation by setting the Auto Neg Enable bit and
     * the Auto Neg Restart bit in the PHY control register.
     */
    ret_val = e1000_read_phy_reg(hw, PHY_CTRL, &phy_data);
    if (ret_val)
        return ret_val;

    phy_data |= (MII_CR_AUTO_NEG_EN | MII_CR_RESTART_AUTO_NEG);
    ret_val = e1000_write_phy_reg(hw, PHY_CTRL, phy_data);
    if (ret_val)
        return ret_val;

    return E1000_SUCCESS;
}

/******************************************************************************
* Detects which PHY is present and setup the speed and duplex
*
* hw - Struct containing variables accessed by shared code
******************************************************************************/
static int32_t
e1000_setup_copper_link(struct e1000_hw *hw)
{
    int32_t ret_val;
    uint16_t i;
    uint16_t phy_data;

    DEBUGFUNC("e1000_setup_copper_link");

    /* Check if it is a valid PHY and set PHY mode if necessary. */
    ret_val = e1000_copper_link_preconfig(hw);
    if (ret_val)
        return ret_val;

    {
        ret_val = e1000_copper_link_igp_setup(hw);
        if (ret_val)
            return ret_val;
    }

    {
        /* Setup autoneg and flow control advertisement
          * and perform autonegotiation */
        ret_val = e1000_copper_link_autoneg(hw);
        if (ret_val)
            return ret_val;
    }

    /* Check link status. Wait up to 100 microseconds for link to become
     * valid.
     */
    for (i = 0; i < 10; i++) {
        ret_val = e1000_read_phy_reg(hw, PHY_STATUS, &phy_data);
        if (ret_val)
            return ret_val;
        ret_val = e1000_read_phy_reg(hw, PHY_STATUS, &phy_data);
        if (ret_val)
            return ret_val;

        e1000_udelay(10);
    }

    DEBUGOUT("Unable to establish link!!!\n");
    return E1000_SUCCESS;
}

/******************************************************************************
* Configures PHY autoneg and flow control advertisement settings
*
* hw - Struct containing variables accessed by shared code
******************************************************************************/
int32_t
e1000_phy_setup_autoneg(struct e1000_hw *hw)
{
    int32_t ret_val;
    uint16_t mii_autoneg_adv_reg;
    uint16_t mii_1000t_ctrl_reg;

    DEBUGFUNC("e1000_phy_setup_autoneg");

    /* Read the MII Auto-Neg Advertisement Register (Address 4). */
    ret_val = e1000_read_phy_reg(hw, PHY_AUTONEG_ADV, &mii_autoneg_adv_reg);
    if (ret_val)
        return ret_val;

    {
        /* Read the MII 1000Base-T Control Register (Address 9). */
        ret_val = e1000_read_phy_reg(hw, PHY_1000T_CTRL, &mii_1000t_ctrl_reg);
        if (ret_val)
            return ret_val;
    }

    /* Need to parse both autoneg_advertised and fc and set up
     * the appropriate PHY registers.  First we will parse for
     * autoneg_advertised software override.  Since we can advertise
     * a plethora of combinations, we need to check each bit
     * individually.
     */

    /* First we clear all the 10/100 mb speed bits in the Auto-Neg
     * Advertisement Register (Address 4) and the 1000 mb speed bits in
     * the  1000Base-T Control Register (Address 9).
     */
    mii_autoneg_adv_reg &= ~REG4_SPEED_MASK;
    mii_1000t_ctrl_reg &= ~REG9_SPEED_MASK;

    DEBUGOUT1("autoneg_advertised %x\n", hw->autoneg_advertised);

    /* Do we want to advertise 10 Mb Half Duplex? */
    {
        DEBUGOUT("Advertise 10mb Half duplex\n");
        mii_autoneg_adv_reg |= NWAY_AR_10T_HD_CAPS;
    }

    /* Do we want to advertise 10 Mb Full Duplex? */
    {
        DEBUGOUT("Advertise 10mb Full duplex\n");
        mii_autoneg_adv_reg |= NWAY_AR_10T_FD_CAPS;
    }

    /* Do we want to advertise 100 Mb Half Duplex? */
    {
        DEBUGOUT("Advertise 100mb Half duplex\n");
        mii_autoneg_adv_reg |= NWAY_AR_100TX_HD_CAPS;
    }

    /* Do we want to advertise 100 Mb Full Duplex? */
    {
        DEBUGOUT("Advertise 100mb Full duplex\n");
        mii_autoneg_adv_reg |= NWAY_AR_100TX_FD_CAPS;
    }

    /* Do we want to advertise 1000 Mb Full Duplex? */
    {
        DEBUGOUT("Advertise 1000mb Full duplex\n");
        mii_1000t_ctrl_reg |= CR_1000T_FD_CAPS;
    }

    /* Check for a software override of the flow control settings, and
     * setup the PHY advertisement registers accordingly.  If
     * auto-negotiation is enabled, then software will have to set the
     * "PAUSE" bits to the correct value in the Auto-Negotiation
     * Advertisement Register (PHY_AUTONEG_ADV) and re-start auto-negotiation.
     *
     * The possible values of the "fc" parameter are:
     *      0:  Flow control is completely disabled
     *      1:  Rx flow control is enabled (we can receive pause frames
     *          but not send pause frames).
     *      2:  Tx flow control is enabled (we can send pause frames
     *          but we do not support receiving pause frames).
     *      3:  Both Rx and TX flow control (symmetric) are enabled.
     *  other:  No software override.  The flow control configuration
     *          in the EEPROM is used.
     */
    {
        /* Flow control (RX & TX) is completely disabled by a
         * software over-ride.
         */
        mii_autoneg_adv_reg &= ~(NWAY_AR_ASM_DIR | NWAY_AR_PAUSE);
    }

    ret_val = e1000_write_phy_reg(hw, PHY_AUTONEG_ADV, mii_autoneg_adv_reg);
    if (ret_val)
        return ret_val;

    DEBUGOUT1("Auto-Neg Advertising %x\n", mii_autoneg_adv_reg);

    {
        ret_val = e1000_write_phy_reg(hw, PHY_1000T_CTRL, mii_1000t_ctrl_reg);
        if (ret_val)
            return ret_val;
    }

    return E1000_SUCCESS;
}

/*****************************************************************************
* Reads the value from a PHY register, if the value is on a specific non zero
* page, sets the page first.
* hw - Struct containing variables accessed by shared code
* reg_addr - address of the PHY register to read
******************************************************************************/
int32_t
e1000_read_phy_reg(struct e1000_hw *hw,
                   uint32_t reg_addr,
                   uint16_t *phy_data)
{
    uint32_t ret_val;
    uint16_t swfw;

    DEBUGFUNC("e1000_read_phy_reg");

    swfw = E1000_SWFW_PHY0_SM;
    if (e1000_get_hw_eeprom_semaphore(hw))
        return -E1000_ERR_SWFW_SYNC;

    if ((reg_addr > MAX_PHY_MULTI_PAGE_REG)) {
        ret_val = e1000_write_phy_reg_ex(hw, IGP01E1000_PHY_PAGE_SELECT,
                                         (uint16_t)reg_addr);
        if (ret_val) {
            e1000_put_hw_eeprom_semaphore(hw);
            return ret_val;
        }
    }
    ret_val = e1000_read_phy_reg_ex(hw, MAX_PHY_REG_ADDRESS & reg_addr,
                                    phy_data);

    e1000_put_hw_eeprom_semaphore(hw);
    return ret_val;
}

static int32_t
e1000_read_phy_reg_ex(struct e1000_hw *hw, uint32_t reg_addr,
                      uint16_t *phy_data)
{
    uint32_t i;
    uint32_t mdic = 0;
    const uint32_t phy_addr = 1;

    DEBUGFUNC("e1000_read_phy_reg_ex");

    if (reg_addr > MAX_PHY_REG_ADDRESS) {
        DEBUGOUT1("PHY Address %d is out of range\n", reg_addr);
        return -E1000_ERR_PARAM;
    }

    {
        /* Set up Op-code, Phy Address, and register address in the MDI
         * Control register.  The MAC will take care of interfacing with the
         * PHY to retrieve the desired data.
         */
        mdic = ((reg_addr << E1000_MDIC_REG_SHIFT) |
                (phy_addr << E1000_MDIC_PHY_SHIFT) |
                (E1000_MDIC_OP_READ));

        E1000_WRITE_REG(hw, MDIC, mdic);

        /* Poll the ready bit to see if the MDI read completed */
        for (i = 0; i < 64; i++) {
            e1000_udelay(50);
            mdic = E1000_READ_REG(hw, MDIC);
            if (mdic & E1000_MDIC_READY) break;
        }
        if (!(mdic & E1000_MDIC_READY)) {
            DEBUGOUT("MDI Read did not complete\n");
            return -E1000_ERR_PHY;
        }
        if (mdic & E1000_MDIC_ERROR) {
            DEBUGOUT("MDI Error\n");
            return -E1000_ERR_PHY;
        }
        *phy_data = (uint16_t) mdic;
    }
    return E1000_SUCCESS;
}

/******************************************************************************
* Writes a value to a PHY register
*
* hw - Struct containing variables accessed by shared code
* reg_addr - address of the PHY register to write
* data - data to write to the PHY
******************************************************************************/
int32_t
e1000_write_phy_reg(struct e1000_hw *hw, uint32_t reg_addr,
                    uint16_t phy_data)
{
    uint32_t ret_val;
    uint16_t swfw;

    DEBUGFUNC("e1000_write_phy_reg");

    {
        swfw = E1000_SWFW_PHY0_SM;
    }
    if (e1000_get_hw_eeprom_semaphore(hw))
        return -E1000_ERR_SWFW_SYNC;

    if ((reg_addr > MAX_PHY_MULTI_PAGE_REG)) {
        ret_val = e1000_write_phy_reg_ex(hw, IGP01E1000_PHY_PAGE_SELECT,
                                         (uint16_t)reg_addr);
        if (ret_val) {
            e1000_put_hw_eeprom_semaphore(hw);
            return ret_val;
        }
    }

    ret_val = e1000_write_phy_reg_ex(hw, MAX_PHY_REG_ADDRESS & reg_addr,
                                     phy_data);

    e1000_put_hw_eeprom_semaphore(hw);
    return ret_val;
}

static int32_t
e1000_write_phy_reg_ex(struct e1000_hw *hw, uint32_t reg_addr,
                       uint16_t phy_data)
{
    uint32_t i;
    uint32_t mdic = 0;
    const uint32_t phy_addr = 1;

    DEBUGFUNC("e1000_write_phy_reg_ex");

    if (reg_addr > MAX_PHY_REG_ADDRESS) {
        DEBUGOUT1("PHY Address %d is out of range\n", reg_addr);
        return -E1000_ERR_PARAM;
    }

    {
        /* Set up Op-code, Phy Address, register address, and data intended
         * for the PHY register in the MDI Control register.  The MAC will take
         * care of interfacing with the PHY to send the desired data.
         */
        mdic = (((uint32_t) phy_data) |
                (reg_addr << E1000_MDIC_REG_SHIFT) |
                (phy_addr << E1000_MDIC_PHY_SHIFT) |
                (E1000_MDIC_OP_WRITE));

        E1000_WRITE_REG(hw, MDIC, mdic);

        /* Poll the ready bit to see if the MDI read completed */
        for (i = 0; i < 641; i++) {
            e1000_udelay(5);
            mdic = E1000_READ_REG(hw, MDIC);
            if (mdic & E1000_MDIC_READY) break;
        }
        if (!(mdic & E1000_MDIC_READY)) {
            DEBUGOUT("MDI Write did not complete\n");
            return -E1000_ERR_PHY;
        }
    }

    return E1000_SUCCESS;
}

/******************************************************************************
* Returns the PHY to the power-on reset state
*
* hw - Struct containing variables accessed by shared code
******************************************************************************/
int32_t
e1000_phy_hw_reset(struct e1000_hw *hw)
{
    uint32_t ctrl;
    int32_t ret_val;
    uint16_t swfw;

    DEBUGFUNC("e1000_phy_hw_reset");

    /* In the case of the phy reset being blocked, it's not an error, we
     * simply return success without performing the reset. */
    ret_val = e1000_check_phy_reset_block(hw);
    if (ret_val)
        return E1000_SUCCESS;

    DEBUGOUT("Resetting Phy...\n");

    {
        swfw = E1000_SWFW_PHY0_SM;
        if (e1000_get_hw_eeprom_semaphore(hw)) {
            DEBUGOUT("Unable to acquire swfw sync\n");
            return -E1000_ERR_SWFW_SYNC;
        }
        /* Read the device control register and assert the E1000_CTRL_PHY_RST
         * bit. Then, take it out of reset.
         * For pre-e1000_82571 hardware, we delay for 10ms between the assert
         * and deassert.  For e1000_82571 hardware and later, we instead delay
         * for 50us between and 10ms after the deassertion.
         */
        ctrl = E1000_READ_REG(hw, CTRL);
        E1000_WRITE_REG(hw, CTRL, ctrl | E1000_CTRL_PHY_RST);
        E1000_WRITE_FLUSH(hw);

        e1000_udelay(100);

        E1000_WRITE_REG(hw, CTRL, ctrl);
        E1000_WRITE_FLUSH(hw);

        e1000_mdelay(10);

        e1000_put_hw_eeprom_semaphore(hw);
    }
    e1000_udelay(150);

    /* Wait for FW to finish PHY configuration. */
    ret_val = e1000_get_phy_cfg_done(hw);
    if (ret_val != E1000_SUCCESS)
        return ret_val;

    return ret_val;
}

/******************************************************************************
* Resets the PHY
*
* hw - Struct containing variables accessed by shared code
*
* Sets bit 15 of the MII Control register
******************************************************************************/
int32_t
e1000_phy_reset(struct e1000_hw *hw)
{
    int32_t ret_val;

    DEBUGFUNC("e1000_phy_reset");

    /* In the case of the phy reset being blocked, it's not an error, we
     * simply return success without performing the reset. */
    ret_val = e1000_check_phy_reset_block(hw);
    if (ret_val)
        return E1000_SUCCESS;

    {
        ret_val = e1000_phy_hw_reset(hw);
        if (ret_val)
            return ret_val;
    }

    return E1000_SUCCESS;
}

/******************************************************************************
 * Raises the EEPROM's clock input.
 *
 * hw - Struct containing variables accessed by shared code
 * eecd - EECD's current value
 *****************************************************************************/
static void
e1000_raise_ee_clk(struct e1000_hw *hw,
                   uint32_t *eecd)
{
    /* Raise the clock input to the EEPROM (by setting the SK bit), and then
     * wait <delay> microseconds.
     */
    *eecd = *eecd | E1000_EECD_SK;
    E1000_WRITE_REG(hw, EECD, *eecd);
    E1000_WRITE_FLUSH(hw);
    e1000_udelay(1);
}

/******************************************************************************
 * Lowers the EEPROM's clock input.
 *
 * hw - Struct containing variables accessed by shared code
 * eecd - EECD's current value
 *****************************************************************************/
static void
e1000_lower_ee_clk(struct e1000_hw *hw,
                   uint32_t *eecd)
{
    /* Lower the clock input to the EEPROM (by clearing the SK bit), and then
     * wait 50 microseconds.
     */
    *eecd = *eecd & ~E1000_EECD_SK;
    E1000_WRITE_REG(hw, EECD, *eecd);
    E1000_WRITE_FLUSH(hw);
    e1000_udelay(1);
}

/******************************************************************************
 * Shift data bits out to the EEPROM.
 *
 * hw - Struct containing variables accessed by shared code
 * data - data to send to the EEPROM
 * count - number of bits to shift out
 *****************************************************************************/
static void
e1000_shift_out_ee_bits(struct e1000_hw *hw,
                        uint16_t data,
                        uint16_t count)
{
    uint32_t eecd;
    uint32_t mask;

    /* We need to shift "count" bits out to the EEPROM. So, value in the
     * "data" parameter will be shifted out to the EEPROM one bit at a time.
     * In order to do this, "data" must be broken down into bits.
     */
    mask = 0x01 << (count - 1);
    eecd = E1000_READ_REG(hw, EECD);
    {
        eecd |= E1000_EECD_DO;
    }
    do {
        /* A "1" is shifted out to the EEPROM by setting bit "DI" to a "1",
         * and then raising and then lowering the clock (the SK bit controls
         * the clock input to the EEPROM).  A "0" is shifted out to the EEPROM
         * by setting "DI" to "0" and then raising and then lowering the clock.
         */
        eecd &= ~E1000_EECD_DI;

        if (data & mask)
            eecd |= E1000_EECD_DI;

        E1000_WRITE_REG(hw, EECD, eecd);
        E1000_WRITE_FLUSH(hw);

        e1000_udelay(1);

        e1000_raise_ee_clk(hw, &eecd);
        e1000_lower_ee_clk(hw, &eecd);

        mask = mask >> 1;

    } while (mask);

    /* We leave the "DI" bit set to "0" when we leave this routine. */
    eecd &= ~E1000_EECD_DI;
    E1000_WRITE_REG(hw, EECD, eecd);
}

/******************************************************************************
 * Shift data bits in from the EEPROM
 *
 * hw - Struct containing variables accessed by shared code
 *****************************************************************************/
static uint16_t
e1000_shift_in_ee_bits(struct e1000_hw *hw,
                       uint16_t count)
{
    uint32_t eecd;
    uint32_t i;
    uint16_t data;

    /* In order to read a register from the EEPROM, we need to shift 'count'
     * bits in from the EEPROM. Bits are "shifted in" by raising the clock
     * input to the EEPROM (setting the SK bit), and then reading the value of
     * the "DO" bit.  During this "shifting in" process the "DI" bit should
     * always be clear.
     */

    eecd = E1000_READ_REG(hw, EECD);

    eecd &= ~(E1000_EECD_DO | E1000_EECD_DI);
    data = 0;

    for (i = 0; i < count; i++) {
        data = data << 1;
        e1000_raise_ee_clk(hw, &eecd);

        eecd = E1000_READ_REG(hw, EECD);

        eecd &= ~(E1000_EECD_DI);
        if (eecd & E1000_EECD_DO)
            data |= 1;

        e1000_lower_ee_clk(hw, &eecd);
    }

    return data;
}

/******************************************************************************
 * Prepares EEPROM for access
 *
 * hw - Struct containing variables accessed by shared code
 *
 * Lowers EEPROM clock. Clears input pin. Sets the chip select pin. This
 * function should be called before issuing a command to the EEPROM.
 *****************************************************************************/
static int32_t
e1000_acquire_eeprom(struct e1000_hw *hw)
{
    uint32_t eecd, i=0;

    DEBUGFUNC("e1000_acquire_eeprom");


    if (e1000_get_hw_eeprom_semaphore(hw))
        return -E1000_ERR_SWFW_SYNC;
    eecd = E1000_READ_REG(hw, EECD);

    {
        /* Request EEPROM Access */
        {
            eecd |= E1000_EECD_REQ;
            E1000_WRITE_REG(hw, EECD, eecd);
            eecd = E1000_READ_REG(hw, EECD);
            while ((!(eecd & E1000_EECD_GNT)) &&
                  (i < E1000_EEPROM_GRANT_ATTEMPTS)) {
                i++;
                e1000_udelay(5);
                eecd = E1000_READ_REG(hw, EECD);
            }
            if (!(eecd & E1000_EECD_GNT)) {
                eecd &= ~E1000_EECD_REQ;
                E1000_WRITE_REG(hw, EECD, eecd);
                DEBUGOUT("Could not acquire EEPROM grant\n");
                e1000_put_hw_eeprom_semaphore(hw);
                return -E1000_ERR_EEPROM;
            }
        }
    }


    /* Setup EEPROM for Read/Write */

    {
        /* Clear SK and CS */
        eecd &= ~(E1000_EECD_CS | E1000_EECD_SK);
        E1000_WRITE_REG(hw, EECD, eecd);
        e1000_udelay(1);
    }

    return E1000_SUCCESS;
}

/******************************************************************************
 * Returns EEPROM to a "standby" state
 *
 * hw - Struct containing variables accessed by shared code
 *****************************************************************************/
static void
e1000_standby_eeprom(struct e1000_hw *hw)
{
    uint32_t eecd;

    eecd = E1000_READ_REG(hw, EECD);

    {
        /* Toggle CS to flush commands */
        eecd |= E1000_EECD_CS;
        E1000_WRITE_REG(hw, EECD, eecd);
        E1000_WRITE_FLUSH(hw);
        e1000_udelay(1);
        eecd &= ~E1000_EECD_CS;
        E1000_WRITE_REG(hw, EECD, eecd);
        E1000_WRITE_FLUSH(hw);
        e1000_udelay(1);
    }
}

/******************************************************************************
 * Terminates a command by inverting the EEPROM's chip select pin
 *
 * hw - Struct containing variables accessed by shared code
 *****************************************************************************/
static void
e1000_release_eeprom(struct e1000_hw *hw)
{
    uint32_t eecd;

    DEBUGFUNC("e1000_release_eeprom");

    eecd = E1000_READ_REG(hw, EECD);

    {
        eecd |= E1000_EECD_CS;  /* Pull CS high */
        eecd &= ~E1000_EECD_SK; /* Lower SCK */

        E1000_WRITE_REG(hw, EECD, eecd);

        e1000_udelay(1);
    }

    /* Stop requesting EEPROM access */
    {
        eecd &= ~E1000_EECD_REQ;
        E1000_WRITE_REG(hw, EECD, eecd);
    }

    e1000_put_hw_eeprom_semaphore(hw);
}

/******************************************************************************
 * Reads a 16 bit word from the EEPROM.
 *
 * hw - Struct containing variables accessed by shared code
 *****************************************************************************/
static int32_t
e1000_spi_eeprom_ready(struct e1000_hw *hw)
{
    uint16_t retry_count = 0;
    uint8_t spi_stat_reg;

    DEBUGFUNC("e1000_spi_eeprom_ready");

    /* Read "Status Register" repeatedly until the LSB is cleared.  The
     * EEPROM will signal that the command has been completed by clearing
     * bit 0 of the internal status register.  If it's not cleared within
     * 5 milliseconds, then error out.
     */
    retry_count = 0;
    do {
        e1000_shift_out_ee_bits(hw, EEPROM_RDSR_OPCODE_SPI,
                                8);
        spi_stat_reg = (uint8_t)e1000_shift_in_ee_bits(hw, 8);
        if (!(spi_stat_reg & EEPROM_STATUS_RDY_SPI))
            break;

        e1000_udelay(5);
        retry_count += 5;

        e1000_standby_eeprom(hw);
    } while (retry_count < EEPROM_MAX_RETRY_SPI);

    /* ATMEL SPI write time could vary from 0-20mSec on 3.3V devices (and
     * only 0-5mSec on 5V devices)
     */
    if (retry_count >= EEPROM_MAX_RETRY_SPI) {
        DEBUGOUT("SPI EEPROM Status error\n");
        return -E1000_ERR_EEPROM;
    }

    return E1000_SUCCESS;
}

/******************************************************************************
 * Reads a 16 bit word from the EEPROM.
 *
 * hw - Struct containing variables accessed by shared code
 * offset - offset of  word in the EEPROM to read
 * data - word read from the EEPROM
 * words - number of words to read
 *****************************************************************************/
int32_t
e1000_read_eeprom(struct e1000_hw *hw,
                  uint16_t offset,
                  uint16_t words,
                  uint16_t *data)
{
    uint32_t i = 0;

    DEBUGFUNC("e1000_read_eeprom");

    /* A check for invalid values:  offset too large, too many words, and not
     * enough words.
     */
    if ((offset >= 2048) || (words > 2048 - offset) ||
       (words == 0)) {
        DEBUGOUT2("\"words\" parameter out of bounds. Words = %d, size = %d\n", offset, 2048);
        return -E1000_ERR_EEPROM;
    }

    /* EEPROM's that don't use EERD to read require us to bit-bang the SPI
     * directly. In this case, we need to acquire the EEPROM so that
     * FW or other port software does not interrupt.
     */
    {
        /* Prepare the EEPROM for bit-bang reading */
        if (e1000_acquire_eeprom(hw) != E1000_SUCCESS)
            return -E1000_ERR_EEPROM;
    }


    /* Set up the SPI or Microwire EEPROM for bit-bang reading.  We have
     * acquired the EEPROM at this point, so any returns should relase it */
    {
        uint16_t word_in;
        uint8_t read_opcode = EEPROM_READ_OPCODE_SPI;

        if (e1000_spi_eeprom_ready(hw)) {
            e1000_release_eeprom(hw);
            return -E1000_ERR_EEPROM;
        }


        e1000_standby_eeprom(hw);

        /* Send the READ command (opcode + addr)  */
        e1000_shift_out_ee_bits(hw, read_opcode, 8);
        e1000_shift_out_ee_bits(hw, (uint16_t)(offset*2), 16);

        /* Read the data.  The address of the eeprom internally increments with
         * each byte (spi) being read, saving on the overhead of eeprom setup
         * and tear-down.  The address counter will roll over if reading beyond
         * the size of the eeprom, thus allowing the entire memory to be read
         * starting from any offset. */
        for (i = 0; i < words; i++) {
            word_in = e1000_shift_in_ee_bits(hw, 16);
            data[i] = (word_in >> 8) | (word_in << 8);
        }
    }

    /* End this read operation */
    e1000_release_eeprom(hw);

    return E1000_SUCCESS;
}

/******************************************************************************
 * Reads the adapter's MAC address from the EEPROM and inverts the LSB for the
 * second function of dual function devices
 *
 * hw - Struct containing variables accessed by shared code
 *****************************************************************************/
int32_t
e1000_read_mac_addr(struct e1000_hw * hw)
{
    uint16_t offset;
    uint16_t eeprom_data, i;

    DEBUGFUNC("e1000_read_mac_addr");

    for (i = 0; i < NODE_ADDRESS_SIZE; i += 2) {
        offset = i >> 1;
        if (e1000_read_eeprom(hw, offset, 1, &eeprom_data) < 0) {
            DEBUGOUT("EEPROM Read Error\n");
            return -E1000_ERR_EEPROM;
        }
        hw->perm_mac_addr[i] = (uint8_t) (eeprom_data & 0x00FF);
        hw->perm_mac_addr[i+1] = (uint8_t) (eeprom_data >> 8);
    }

    for (i = 0; i < NODE_ADDRESS_SIZE; i++)
		    hw->mac_addr[i] = hw->perm_mac_addr[i];

		return E1000_SUCCESS;
}

/******************************************************************************
 * Initializes receive address filters.
 *
 * hw - Struct containing variables accessed by shared code
 *
 * Places the MAC address in receive address register 0 and clears the rest
 * of the receive addresss registers. Clears the multicast table. Assumes
 * the receiver is in reset when the routine is called.
 *****************************************************************************/
static void
e1000_init_rx_addrs(struct e1000_hw *hw)
{
    uint32_t i;
    uint32_t rar_num;

    DEBUGFUNC("e1000_init_rx_addrs");

    /* Setup the receive address. */
    DEBUGOUT("Programming MAC Address into RAR[0]\n");

    e1000_rar_set(hw, hw->mac_addr, 0);

    rar_num = E1000_RAR_ENTRIES;

    /* Zero out the other 15 receive addresses. */
    DEBUGOUT("Clearing RAR[1-15]\n");
    for (i = 1; i < rar_num; i++) {
        E1000_WRITE_REG_ARRAY(hw, RA, (i << 1), 0);
        E1000_WRITE_FLUSH(hw);
        E1000_WRITE_REG_ARRAY(hw, RA, ((i << 1) + 1), 0);
        E1000_WRITE_FLUSH(hw);
    }
}

/******************************************************************************
 * Puts an ethernet address into a receive address register.
 *
 * hw - Struct containing variables accessed by shared code
 * addr - Address to put into receive address register
 * index - Receive address register to write
 *****************************************************************************/
void
e1000_rar_set(struct e1000_hw *hw,
              uint8_t *addr,
              uint32_t index)
{
    uint32_t rar_low, rar_high;

    /* HW expects these in little endian so we reverse the byte order
     * from network order (big endian) to little endian
     */
    rar_low = ((uint32_t) addr[0] |
               ((uint32_t) addr[1] << 8) |
               ((uint32_t) addr[2] << 16) | ((uint32_t) addr[3] << 24));
    rar_high = ((uint32_t) addr[4] | ((uint32_t) addr[5] << 8));

    /* Disable Rx and flush all Rx frames before enabling RSS to avoid Rx
     * unit hang.
     *
     * Description:
     * If there are any Rx frames queued up or otherwise present in the HW
     * before RSS is enabled, and then we enable RSS, the HW Rx unit will
     * hang.  To work around this issue, we have to disable receives and
     * flush out all Rx frames before we enable RSS. To do so, we modify we
     * redirect all Rx traffic to manageability and then reset the HW.
     * This flushes away Rx frames, and (since the redirections to
     * manageability persists across resets) keeps new ones from coming in
     * while we work.  Then, we clear the Address Valid AV bit for all MAC
     * addresses and undo the re-direction to manageability.
     * Now, frames are coming in again, but the MAC won't accept them, so
     * far so good.  We now proceed to initialize RSS (if necessary) and
     * configure the Rx unit.  Last, we re-enable the AV bits and continue
     * on our merry way.
     */
    {
        /* Indicate to hardware the Address is Valid. */
        rar_high |= E1000_RAH_AV;
    }

    E1000_WRITE_REG_ARRAY(hw, RA, (index << 1), rar_low);
    E1000_WRITE_FLUSH(hw);
    E1000_WRITE_REG_ARRAY(hw, RA, ((index << 1) + 1), rar_high);
    E1000_WRITE_FLUSH(hw);
}

/******************************************************************************
 * Clears the VLAN filer table
 *
 * hw - Struct containing variables accessed by shared code
 *****************************************************************************/
static void
e1000_clear_vfta(struct e1000_hw *hw)
{
    uint32_t offset;
    uint32_t vfta_value = 0;
    uint32_t vfta_offset = 0;
    uint32_t vfta_bit_in_reg = 0;

    for (offset = 0; offset < E1000_VLAN_FILTER_TBL_SIZE; offset++) {
        /* If the offset we want to clear is the same offset of the
         * manageability VLAN ID, then clear all bits except that of the
         * manageability unit */
        vfta_value = (offset == vfta_offset) ? vfta_bit_in_reg : 0;
        E1000_WRITE_REG_ARRAY(hw, VFTA, offset, vfta_value);
        E1000_WRITE_FLUSH(hw);
    }
}

/*****************************************************************************
 *
 * This function sets the lplu d0 state according to the active flag.  When
 * activating lplu this function also disables smart speed and vise versa.
 * lplu will not be activated unless the device autonegotiation advertisment
 * meets standards of either 10 or 10/100 or 10/100/1000 at all duplexes.
 * hw: Struct containing variables accessed by shared code
 * active - true to enable lplu false to disable lplu.
 *
 * returns: - E1000_ERR_PHY if fail to read/write the PHY
 *            E1000_SUCCESS at any other case.
 *
 ****************************************************************************/

static int32_t
e1000_set_d0_lplu_state(struct e1000_hw *hw,
                        bool active)
{
    int32_t ret_val;
    uint16_t phy_data;
    DEBUGFUNC("e1000_set_d0_lplu_state");

    {
        ret_val = e1000_read_phy_reg(hw, IGP02E1000_PHY_POWER_MGMT, &phy_data);
        if (ret_val)
            return ret_val;
    }

    {
        {
            phy_data &= ~IGP02E1000_PM_D0_LPLU;
            ret_val = e1000_write_phy_reg(hw, IGP02E1000_PHY_POWER_MGMT, phy_data);
            if (ret_val)
                return ret_val;
        }
    }
    return E1000_SUCCESS;
}

/***************************************************************************
 *
 * Disables PCI-Express master access.
 *
 * hw: Struct containing variables accessed by shared code
 *
 * returns: - none.
 *
 ***************************************************************************/
static void
e1000_set_pci_express_master_disable(struct e1000_hw *hw)
{
    uint32_t ctrl;

    DEBUGFUNC("e1000_set_pci_express_master_disable");

    ctrl = E1000_READ_REG(hw, CTRL);
    ctrl |= E1000_CTRL_GIO_MASTER_DISABLE;
    E1000_WRITE_REG(hw, CTRL, ctrl);
}

/*******************************************************************************
 *
 * Disables PCI-Express master access and verifies there are no pending requests
 *
 * hw: Struct containing variables accessed by shared code
 *
 * returns: - E1000_ERR_MASTER_REQUESTS_PENDING if master disable bit hasn't
 *            caused the master requests to be disabled.
 *            E1000_SUCCESS master requests disabled.
 *
 ******************************************************************************/
int32_t
e1000_disable_pciex_master(struct e1000_hw *hw)
{
    int32_t timeout = MASTER_DISABLE_TIMEOUT;   /* 80ms */

    DEBUGFUNC("e1000_disable_pciex_master");

    e1000_set_pci_express_master_disable(hw);

    while (timeout) {
        if (!(E1000_READ_REG(hw, STATUS) & E1000_STATUS_GIO_MASTER_ENABLE))
            break;
        else
            e1000_udelay(100);
        timeout--;
    }

    if (!timeout) {
        DEBUGOUT("Master requests are pending.\n");
        return -E1000_ERR_MASTER_REQUESTS_PENDING;
    }

    return E1000_SUCCESS;
}

/*******************************************************************************
 *
 * Check for EEPROM Auto Read bit done.
 *
 * hw: Struct containing variables accessed by shared code
 *
 * returns: - E1000_ERR_RESET if fail to reset MAC
 *            E1000_SUCCESS at any other case.
 *
 ******************************************************************************/
static int32_t
e1000_get_auto_rd_done(struct e1000_hw *hw)
{
    int32_t timeout = AUTO_READ_DONE_TIMEOUT;

    DEBUGFUNC("e1000_get_auto_rd_done");

    {
        while (timeout) {
            if (E1000_READ_REG(hw, EECD) & E1000_EECD_AUTO_RD)
                break;
            else e1000_msleep(1);
            timeout--;
        }

        if (!timeout) {
            DEBUGOUT("Auto read by HW from EEPROM has not completed.\n");
            return -E1000_ERR_RESET;
        }
    }

    return E1000_SUCCESS;
}

/***************************************************************************
 * Checks if the PHY configuration is done
 *
 * hw: Struct containing variables accessed by shared code
 *
 * returns: - E1000_ERR_RESET if fail to reset MAC
 *            E1000_SUCCESS at any other case.
 *
 ***************************************************************************/
static int32_t
e1000_get_phy_cfg_done(struct e1000_hw *hw)
{
    int32_t timeout = PHY_CFG_TIMEOUT * 1000;
    uint32_t cfg_mask = E1000_EEPROM_CFG_DONE;

    DEBUGFUNC("e1000_get_phy_cfg_done");

    {
        while (timeout) {
            if (E1000_READ_REG(hw, EEMNGCTL) & cfg_mask)
                break;
            else
                e1000_msleep(1);
            timeout--;
        }
        if (!timeout) {
            DEBUGOUT("MNG configuration cycle has not completed.\n");
            return -E1000_ERR_RESET;
        }
    }

    return E1000_SUCCESS;
}

/***************************************************************************
 *
 * Using the combination of SMBI and SWESMBI semaphore bits when resetting
 * adapter or Eeprom access.
 *
 * hw: Struct containing variables accessed by shared code
 *
 * returns: - E1000_ERR_EEPROM if fail to access EEPROM.
 *            E1000_SUCCESS at any other case.
 *
 ***************************************************************************/
static int32_t
e1000_get_hw_eeprom_semaphore(struct e1000_hw *hw)
{
    int32_t timeout;
    uint32_t swsm;

    DEBUGFUNC("e1000_get_hw_eeprom_semaphore");

    /* Get the FW semaphore. */
    timeout = 2048 + 1;
    while (timeout) {
        swsm = E1000_READ_REG(hw, SWSM);
        swsm |= E1000_SWSM_SWESMBI;
        E1000_WRITE_REG(hw, SWSM, swsm);
        /* if we managed to set the bit we got the semaphore. */
        swsm = E1000_READ_REG(hw, SWSM);
        if (swsm & E1000_SWSM_SWESMBI)
            break;

        e1000_udelay(50);
        timeout--;
    }

    if (!timeout) {
        /* Release semaphores */
        e1000_put_hw_eeprom_semaphore(hw);
        DEBUGOUT("Driver can't access the Eeprom - SWESMBI bit is set.\n");
        return -E1000_ERR_EEPROM;
    }

    return E1000_SUCCESS;
}

/***************************************************************************
 * This function clears HW semaphore bits.
 *
 * hw: Struct containing variables accessed by shared code
 *
 * returns: - None.
 *
 ***************************************************************************/
static void
e1000_put_hw_eeprom_semaphore(struct e1000_hw *hw)
{
    uint32_t swsm;

    DEBUGFUNC("e1000_put_hw_eeprom_semaphore");

    swsm = E1000_READ_REG(hw, SWSM);
    swsm &= ~(E1000_SWSM_SWESMBI);
    E1000_WRITE_REG(hw, SWSM, swsm);
}

/******************************************************************************
 * Checks if PHY reset is blocked due to SOL/IDER session, for example.
 * Returning E1000_BLK_PHY_RESET isn't necessarily an error.  But it's up to
 * the caller to figure out how to deal with it.
 *
 * hw - Struct containing variables accessed by shared code
 *
 * returns: - E1000_BLK_PHY_RESET
 *            E1000_SUCCESS
 *
 *****************************************************************************/
int32_t
e1000_check_phy_reset_block(struct e1000_hw *hw)
{
    uint32_t manc = 0;

    manc = E1000_READ_REG(hw, MANC);
    return (manc & E1000_MANC_BLK_PHY_RST_ON_IDE) ?
        E1000_BLK_PHY_RESET : E1000_SUCCESS;
}


static void e1000_pci_set_master(pci_device_t *nwdevice)
{
        uint32_t cmd;

        xmhf_baseplatform_arch_x86_pci_type1_read(nwdevice->bus,
						nwdevice->dev,
						nwdevice->func,
						PCI_CONF_HDR_IDX_COMMAND,
						sizeof(uint16_t),
						&cmd);
        cmd |= PCI_COMMAND_MASTER;
        xmhf_baseplatform_arch_x86_pci_type1_write(nwdevice->bus,
						nwdevice->dev,
						nwdevice->func,
						PCI_CONF_HDR_IDX_COMMAND,
						sizeof(uint16_t),
						cmd);
}

static void e1000_pci_disable_master(pci_device_t *nwdevice)
{
        uint16_t cmd;

        xmhf_baseplatform_arch_x86_pci_type1_read(nwdevice->bus,
						nwdevice->dev,
						nwdevice->func,
						PCI_CONF_HDR_IDX_COMMAND,
						sizeof(uint16_t),
						&cmd);
        cmd &= ~PCI_COMMAND_MASTER;
        xmhf_baseplatform_arch_x86_pci_type1_write(nwdevice->bus,
						nwdevice->dev,
						nwdevice->func,
						PCI_CONF_HDR_IDX_COMMAND,
						sizeof(uint16_t),
						cmd);

}














//////
// e1000e network card top-level support functions
//////




void e1000_reset(void);
static int e1000_setup_tx_resources(struct e1000_tx_ring *tx_ring);
static int e1000_probe(pci_device_t *nwdevice);
static int e1000_open(void);
static void e1000_configure_tx(void);
void e1000_xmit(unsigned short tail);
void e1000_wait4xmit(void);
static void e1000_irq_disable(void);


void e1000_mdelay1(unsigned int msec)
{
/* first value is 1GHz,
 * second is seconds to wait
 * the third one depends how fast your CPU is
 */
	uint64_t cycles = E1000_TIMEOUT_1MS * msec;
	uint64_t diff;
	uint64_t tscbefore, tscafter;
	tscbefore = CASM_FUNCCALL(rdtsc64, CASM_NOPARAM);
	do
	{
		tscafter = CASM_FUNCCALL(rdtsc64, CASM_NOPARAM);
		diff = tscafter - tscbefore;
	} while (diff < cycles);
}


void e1000_reset(void)
{
	uint32_t pba = 0;
	uint16_t phy_data = 0;

	/* Repartition Pba for greater than 9k mtu
	 * To take effect CTRL.RST is required.
	 */


	pba = E1000_PBA_38K;

	E1000_WRITE_REG(&e1000_adapt.hw, PBA, pba);

	e1000_adapt.hw.fc_pause_time = E1000_FC_PAUSE_TIME;

	/* Allow time for pending master requests to run */
	e1000_reset_hw(&e1000_adapt.hw);
	E1000_WRITE_REG(&e1000_adapt.hw, WUC, 0);

	if (e1000_init_hw(&e1000_adapt.hw))
		DPRINTK(PROBE, ERR, "Hardware Error\n");

	/* speed up time to link by disabling smart power down, ignore
	 * the return value of this function because there is nothing
	 * different we would do if it failed */
	e1000_read_phy_reg(&e1000_adapt.hw, IGP02E1000_PHY_POWER_MGMT,
	                   &phy_data);
	phy_data &= ~IGP02E1000_PM_SPD;
	e1000_write_phy_reg(&e1000_adapt.hw, IGP02E1000_PHY_POWER_MGMT,
	                    phy_data);
}

/**
 * e1000_probe - Device Initialization Routine
 * @pdev: PCI device information struct
 *
 * Returns 0 on success, negative on failure
 *
 * e1000_probe initializes an adapter identified by a pci_dev structure.
 * The OS initialization, configuring of the adapter private structure,
 * and a hardware reset occur.
 **/

static int e1000_probe(pci_device_t *nwdevice)
{
	unsigned long mmio_start, mmio_len;

	int i, err;
	uint16_t eeprom_data = 0;
	uint32_t ctrl_ext;

	DEBUGQ(0);
	e1000_pci_set_master(&e1000_dev);

	//err = -ENOMEM;

	uberspark_uobjrtl_crt__memset(&e1000_adapt, 0, sizeof(struct e1000_adapter));
	e1000_adapt.msg_enable = 1;

	//TODO: probe base address of this adapter via config space
	e1000_adapt.hw.hw_addr = E1000_HWADDR_BASE;


	/* setup the private structure */
	e1000_irq_disable();

	//err = -EIO;

	e1000_check_phy_reset_block(&e1000_adapt.hw);

	/* before reading the EEPROM, reset the controller to
	 * put the device in a known good starting state */

	e1000_reset_hw(&e1000_adapt.hw);

	/* copy the MAC address out of the EEPROM */
	if (e1000_read_mac_addr(&e1000_adapt.hw)){
		//printf("\nNIC EEPROM Read Error");
		return -1;
	}


	DEBUGQ(0);
	/* Transmit Descriptor Count */
	//e1000_adapt.tx_ring.count = ALIGN(E1000_DESC_COUNT, 2);
	e1000_adapt.tx_ring.count = E1000_DESC_COUNT;

	e1000_read_eeprom(&e1000_adapt.hw,
		EEPROM_INIT_CONTROL3_PORT_A, 1, &eeprom_data);

	//printf("\nMAC address:");
	//e1000_adapt.hw.mac_addr[0]=e1000_adapt.hw.perm_mac_addr[0]=0x00;
	//e1000_adapt.hw.mac_addr[1]=e1000_adapt.hw.perm_mac_addr[1]=0x1B;
	//e1000_adapt.hw.mac_addr[2]=e1000_adapt.hw.perm_mac_addr[2]=0x21;
	//e1000_adapt.hw.mac_addr[3]=e1000_adapt.hw.perm_mac_addr[3]=0x48;
	//e1000_adapt.hw.mac_addr[4]=e1000_adapt.hw.perm_mac_addr[4]=0x09;
	//e1000_adapt.hw.mac_addr[5]=e1000_adapt.hw.perm_mac_addr[5]=0x34;

	//for (i = 0; i < 6; i++)
	//	printf("%02x ", e1000_adapt.hw.mac_addr[i]);

	/* reset the hardware with the new settings */
	e1000_reset();

	/* Let firmware know the driver has taken over */
	ctrl_ext = E1000_READ_REG(&e1000_adapt.hw, CTRL_EXT);
	E1000_WRITE_REG(&e1000_adapt.hw, CTRL_EXT,
			ctrl_ext | E1000_CTRL_EXT_DRV_LOAD);

	DPRINTK(PROBE, INFO, "DEBUG : Intel(R) PRO/1000 Network Connection\n");

	return 0;
}

/**
 * e1000_open - Called when a network interface is made active
 * @netdev: network interface device structure
 *
 * Returns 0 on success, negative value on failure
 *
 * The open entry point is called when a network interface is made
 * active by the system (IFF_UP).  At this point all resources needed
 * for transmit and receive operations are allocated, the interrupt
 * handler is registered with the OS, the watchdog timer is started,
 * and the stack is notified that the interface is ready.
 **/
static int e1000_open(void)
{
	int err = 0;
	uint16_t mii_reg = 0;

	DEBUGQ(0);

	/* allocate transmit descriptors */
	err = e1000_setup_tx_resources(&e1000_adapt.tx_ring);
	if (err) {
		DPRINTK(PROBE, ERR,
			"Allocation for Tx Queue %u failed\n", 0);
		goto err_setup_tx;
	}


	/* Just clear the power down bit to wake the phy back up */
	/* according to the manual, the phy will retain its
	 * settings across a power-down/up cycle */
	e1000_read_phy_reg(&e1000_adapt.hw, PHY_CTRL, &mii_reg);
	mii_reg &= ~MII_CR_POWER_DOWN;
	e1000_write_phy_reg(&e1000_adapt.hw, PHY_CTRL, mii_reg);

	/* before we allocate an interrupt, we must be ready to handle it.
	 * Setting DEBUG_SHIRQ in the kernel makes it fire an interrupt
	 * as soon as we call pci_request_irq, so we have to setup our
	 * clean_rx handler before we do so.  */
	e1000_configure_tx();

	return E1000_SUCCESS;

err_setup_tx:
	return err;
}

/**
 * e1000_setup_tx_resources - allocate Tx resources (Descriptors)
 * @adapter: board private structure
 * @tx_ring:    tx descriptor ring (for a specific queue) to setup
 *
 * Return 0 on success, negative on failure
 **/
static int e1000_setup_tx_resources(struct e1000_tx_ring *tx_ring)
{
	unsigned int i;
	struct e1000_tx_desc *tx_desc = NULL;
	unsigned char *buffer;

	uberspark_uobjrtl_crt__memset(&xcnwlog_desc, 0, sizeof(xcnwlog_desc));

	//setup descriptor table size
	tx_ring->size_desc = tx_ring->count * sizeof(struct e1000_tx_desc);
	tx_ring->size_desc = PAGE_ALIGN_UP4K(tx_ring->size_desc);
	//setup descriptor table base
	tx_ring->desc=&xcnwlog_desc;
	tx_ring->dma_desc=&xcnwlog_desc;

	tx_desc = E1000_TX_DESC(*tx_ring, 0);
	tx_desc->buffer_addr = e1000_cpu_to_le64((unsigned int)&xcnwlog_packet);
	tx_desc->lower.data = e1000_cpu_to_le32(E1000_TXD_CMD_IFCS | E1000_TXD_CMD_EOP | (sizeof(xcnwlog_packet)));
	tx_desc->upper.data = e1000_cpu_to_le32(0);


	/*for (i = 0; i < tx_ring->count * sizeof(struct e1000_tx_desc); i ++)
	{
		printk("%02x ", *(unsigned char *)((unsigned int)tx_ring->desc + i));
		if ((i % 16) == 15)
			printk("\n");
	}*/

	return 0;
}

/**
 * e1000_configure_tx - Configure 8254x Transmit Unit after Reset
 * @adapter: board private structure
 *
 * Configure the Tx unit of the MAC after a reset.
 **/

static void
e1000_configure_tx(void)
{
	uint64_t tdba;
	struct e1000_hw *hw = &e1000_adapt.hw;
	uint32_t tdlen, tctl, tipg, tarc;

	/* Setup the HW Tx Head and Tail descriptor pointers */
	tdba = e1000_adapt.tx_ring.dma_desc;
	//tdlen = e1000_adapt.tx_ring.count * sizeof(struct e1000_tx_desc);
	tdlen = 4096;
	E1000_WRITE_REG(hw, TDLEN, tdlen);
	//E1000_WRITE_REG(hw, TDBAH, (tdba >> 32));
	//E1000_WRITE_REG(hw, TDBAL, (tdba & 0x00000000ffffffffULL));
	E1000_WRITE_REG(hw, TDBAH, 0);
	E1000_WRITE_REG(hw, TDBAL, (uint32_t)e1000_adapt.tx_ring.dma_desc);
	E1000_WRITE_REG(hw, TDT, 0);
	E1000_WRITE_REG(hw, TDH, 0);
	e1000_adapt.tx_ring.tdh = (E1000_TDH);
	e1000_adapt.tx_ring.tdt = (E1000_TDT);

	tipg = DEFAULT_82543_TIPG_IPGT_COPPER;
	tipg |= DEFAULT_82543_TIPG_IPGR1 << E1000_TIPG_IPGR1_SHIFT;
	tipg |= DEFAULT_82543_TIPG_IPGR2 << E1000_TIPG_IPGR2_SHIFT;

	E1000_WRITE_REG(hw, TIPG, tipg);

	/* Set the Tx Interrupt Delay register */
	E1000_WRITE_REG(hw, TIDV, e1000_adapt.tx_int_delay);
	E1000_WRITE_REG(hw, TADV, e1000_adapt.tx_abs_int_delay);

	/* Program the Transmit Control Register */
	tctl = E1000_READ_REG(hw, TCTL);
	tctl &= ~E1000_TCTL_CT;
	tctl |= E1000_TCTL_PSP | E1000_TCTL_RTLC | (E1000_COLLISION_THRESHOLD << E1000_CT_SHIFT);

	tarc = E1000_READ_REG(hw, TARC0);
	/* set the speed mode bit, we'll clear it if we're not at
	 * gigabit link later */
	tarc |= (1 << 21);
	E1000_WRITE_REG(hw, TARC0, tarc);

	/* Setup Transmit Descriptor Settings for eop descriptor */
	e1000_adapt.txd_cmd = E1000_TXD_CMD_EOP | E1000_TXD_CMD_IFCS | E1000_TXD_CMD_RS;
	E1000_WRITE_REG(hw, TCTL, tctl);
}

void e1000_xmit(unsigned short tail)
{
	unsigned int tctl;

	DEBUGQ(tail);

#ifdef E1000_DEBUG_PKTIDX
	{
		static unsigned int idx_init = 0;
		if ((tail != 0) && (idx_init))
		{
			unsigned int i;
			unsigned int idx;
			unsigned char *buffer;
			struct e1000_tx_desc *tx_desc = NULL;

			for (i = 0; i < e1000_adapt.tx_ring.count; i ++)
			{
				tx_desc = E1000_TX_DESC(e1000_adapt.tx_ring, i);
				if ((i % 2) == 0)
				{
					buffer = (unsigned char *)e1000_adapt.tx_ring.buf_header + E1000_HEADER_SIZE *  (i / 2);
					idx = *(unsigned int *)(buffer + 14);
					idx += e1000_adapt.tx_ring.count;
					*(unsigned int *)(buffer + 14) = idx;
				}
			}
		} else
			idx_init = 1;
	}
#endif
	/* enable transmits in the hardware, need to do this
	 * after setting TARC0 */
	tctl = E1000_READ_REG(&e1000_adapt.hw, TCTL);
	tctl |= E1000_TCTL_EN;
	E1000_WRITE_REG(&e1000_adapt.hw, TCTL, tctl);

	e1000_writel(tail, e1000_adapt.hw.hw_addr + e1000_adapt.tx_ring.tdt);
}


uint32_t e1000_check4xmit(void)
{
	unsigned short tail, head;

	tail = e1000_readl(e1000_adapt.hw.hw_addr + e1000_adapt.tx_ring.tdt);
	head = e1000_readl(e1000_adapt.hw.hw_addr + e1000_adapt.tx_ring.tdh);

	if(tail != head)
		return 0;
	else
		return 1;
}


void e1000_wait4xmit(void)
{
	unsigned short tail, head;

	tail = e1000_readl(e1000_adapt.hw.hw_addr + e1000_adapt.tx_ring.tdt);
	DEBUGQ(tail);

	do {
		head = e1000_readl(e1000_adapt.hw.hw_addr + e1000_adapt.tx_ring.tdh);
	} while (head != tail);

}



/**
 * e1000_irq_disable - Mask off interrupt generation on the NIC
 * @adapter: board private structure
 **/

static void e1000_irq_disable(void)
{
	E1000_WRITE_REG(&e1000_adapt.hw, IMC, ~0);
	E1000_WRITE_FLUSH(&e1000_adapt.hw);
}


/////
void e1000_xmitack(void){
	_XDPRINTF_("%s: transmitting...\n", __func__);
	e1000_xmit(1);
	_XDPRINTF_("%s: transmit signal sent, waiting for finish...\n", __func__);
	e1000_wait4xmit();
	_XDPRINTF_("%s: transmit successful\n", __func__);
}

uint32_t e1000_init_module(void)
{
	int ret = 0;
	uint32_t i;


	//TODO: probe PCI bus to figure out b,d,f
	e1000_dev.vendor_id = 0x8086;
	e1000_dev.device_id = 0x10b9;
	e1000_dev.bus = 4;
	e1000_dev.dev = 0;
	e1000_dev.func = 0;

	_XDPRINTF_("%s: probing for ethernet card...\n", __func__);

	DEBUGQ(0);
	ret = e1000_probe(&e1000_dev);

	if (ret < 0)
	   return 0;

	_XDPRINTF_("%s: card found, MAC address=", __func__);
	for (i = 0; i < 6; i++)
		_XDPRINTF_("%02x ", e1000_adapt.hw.mac_addr[i]);
	_XDPRINTF_("\n");


	_XDPRINTF_("%s: opening interface...\n", __func__);
	ret = e1000_open();

	if (ret < 0)
	   return 0;

	_XDPRINTF_("%s: interface opened successfully\n", __func__);


	_XDPRINTF_("%s: waiting for switch...\n", __func__);
	e1000_mdelay1(15 * 1000);
	_XDPRINTF_("%s: ready to xmit...\n", __func__);

	//setup packet header
	xcnwlog_packet.dst_mac[0] = 0xFF;
	xcnwlog_packet.dst_mac[1] = 0xFF;
	xcnwlog_packet.dst_mac[2] = 0xFF;
	xcnwlog_packet.dst_mac[3] = 0xFF;
	xcnwlog_packet.dst_mac[4] = 0xFF;
	xcnwlog_packet.dst_mac[5] = 0xFF;
	xcnwlog_packet.src_mac[0] = e1000_adapt.hw.mac_addr[0];
	xcnwlog_packet.src_mac[1] = e1000_adapt.hw.mac_addr[1];
	xcnwlog_packet.src_mac[2] = e1000_adapt.hw.mac_addr[2];
	xcnwlog_packet.src_mac[3] = e1000_adapt.hw.mac_addr[3];
	xcnwlog_packet.src_mac[4] = e1000_adapt.hw.mac_addr[4];
	xcnwlog_packet.src_mac[5] = e1000_adapt.hw.mac_addr[5];
	xcnwlog_packet.type[0] = 0x80;
	xcnwlog_packet.type[1] = 0x86;

/*	_XDPRINTF_("%s: transmitting...\n", __func__);
	e1000_xmit(1);
	_XDPRINTF_("%s: transmit signal sent, waiting for finish...\n", __func__);
	e1000_wait4xmit();
	_XDPRINTF_("%s: transmit successful\n", __func__);
*/

	return ret;
}



