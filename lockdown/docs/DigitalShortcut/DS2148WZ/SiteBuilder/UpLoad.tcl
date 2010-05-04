##################### Terminal In/Out events ############################
 proc term_out {s} {
    puts -nonewline $::tty(chan) $s
    #append ::tx $s
 }
 #--
 proc term_in { ch } {
      #append ::rx $ch
      switch -regexp -- $ch {
         [\x07]    { bell }
         [\x0A]    { # ignore }
         [\x0D]    { verifyEcho; #-- or interpret response - not used at this moment}
         [\x21]    { armCmd; #-- ! ARM ready for next command - not used at this moment}
         [\x3E]    { spartanCmd; #-- > Spartan is readu for next command}
         default   { #-- append ::tty(line) $ch; #-- do nothing }
     }
 }
 #--
 proc receiver {chan} {
     foreach ch [ split [read $chan] {}] {
         term_in $ch
     }
 }                                                                                     
 #------------------------------------------------------------------------------------------------------
 proc open_tty {} {
    set prms "115200,n,8,1"
    set ::tty(line) ""
    set ::tty(state) "sync1"
    foreach com {[list com1 com6 com7 com4 com5 com2]} {
       if { [catch { set ::tty(chan) [open $com r+]}] == 0 } {
          set ::tty(port) $com; break;
       }
    }
    fconfigure $::tty(chan) -mode $prms -translation binary -buffering none -blocking 0 -ttycontrol {RTS 0 DTR 0}   
    return "$::tty(port): $prms"
 }
 proc close_tty {} {
    close $::tty(chan)
 }                               
 #--
 proc verifyEcho {} {
   # nop
 }
 proc armCmd {ch } {
    append ::tty(line) "!"
 }                        
 
 proc spartanCmd {} {                                                   
    switch -- $::tty(state) {
       "snc1"   { s3Sync1 }
       "snc2"   { s3Sync2 }
       "sSet"   { s3Setup }
       "sPrg"   { s3Program }
       default  { append ::tty(line) ">" }
    }
 }
 proc s3Sync1 {} {
     set ::tty(line) "";      #-- discard all prev chars
     set ::tty(state) "snc2"; #-- next state
     term_out "\x0D";         #-- send CR 
 }
 proc s3Sync2 {} {
     set ::tty(line) "";      #-- discard all prev chars
     set ::tty(state) "sSet"; #-- next state
     term_out "j\x0D";        #-- disable http and CR 
 }
 proc s3Setup {} {
    set ::tty(line) "";      #-- discard all prev chars
    #- chk if there are bytes to send
    #-- convert page number to offset in ::tty(biglist)
    set ix [expr (($::tty(pnum) - 208)* 264 )]; 
    set ::tty(pdata) [lrange $::tty(biglist) $ix $ix+263]
    if { [llength $::tty(pdata)] > 0 } {
       set ::tty(state) "sPrg"; #-- next state
       .upld.t insert end "."
       term_out "b[format %02X $::tty(pnum)]\x0D"
    } else {
       #-- no more data
       set ::tty(state) "sDone"; #-- next state
       incr ::tty(pnum) -1
       .upld.t insert end "\nlast programmed page: $::tty(pnum)\nProgramming Done!\n"
       term_out "op\x0D";        #-- switch off and on power for W5300   
    }
 }
 proc s3Program {} {
    set ::tty(line) "";      #-- discard all prev chars
    set xp [format %02X $::tty(pnum)]
    incr ::tty(pnum)
    
    term_out "w00 "
    foreach xx $::tty(pdata) {
       term_out "$xx "
    }
    set ::tty(state) "sSet"; #-- next state
    term_out "u$xp\x0D"
    #--term_out "\x0D"
 }
 proc main {} {
    set fi [open [file join "$::SiB(srdir)" "SiteBuilderGenerated/site.hex"] r]
    fconfigure $fi -buffering line
    set ::tty(biglist) {}
    while {[gets $fi line] >= 0} {
       foreach x $line {
          lappend ::tty(biglist) $x
       }
    }
    close $fi                                    
    set ::tty(line) ""
    set ::tty(pnum) 208
    set ::tty(pdata) {}
    set ::tty(state) "snc1"
    set numb [llength $::tty(biglist)]
    if { $numb > 0} {
       .upld.t insert end "Programming $numb bytes ( starting from page #208)\n"
       term_out "\x0D"
    } else {
       .upld.t insert end "Nothing to program!\n" 
    }
 }
  
 #-----------------------------------------------------------------------------------------
 #-- Upload window
 #-----------------------------------------------------------------------------------------
 proc buildUpWdw {} {
    toplevel .upld
    wm title .upld "Uplad site" 
    pack [frame .upld.f -relief sunken -borderwidth 1] -anchor w -fill x
    #--button .upld.f.b1 -text "test1" -width 10 -command {puts $::tty(line)}
    #--button .upld.f.b2 -text "sndCR" -width 10 -command {term_out "\x0D"}
    #--eval pack [winfo children .upld.f] -side left
    pack [text .upld.t -wrap word -undo 1] -side top -fill both -expand 1
    wm geom .upld "500x500+150+100"
    focus -force .upld.t
    .upld.t insert end "settings: [open_tty ];\n" 
    fileevent $::tty(chan) readable [list receiver $::tty(chan)]
 }
 #--
 set ::tx ""
 set ::rx ""
 buildUpWdw
 main
  