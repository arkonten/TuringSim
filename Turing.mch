/* A TM can have multiple halting states (although one can be used
   without loss of generality) but we can have a parameter HALT and a
   CONSTRAINT HALT <: STATE, so I suppose we're stuck with one
   only. */

MACHINE Turing(ALPHA,
               tape_blank,
               tape_start,
               STATE,
               init,
               halt)
CONSTRAINTS card(ALPHA) > 2 &
            tape_blank:ALPHA &
            tape_start:ALPHA &
            tape_blank /= tape_start &
            card(STATE) > 0 &
            init:STATE &
            halt:STATE
SETS STATUS = {halted,
               running,
               out_of_time,
               out_of_memory,
               segmantation_fault,
               no_transition_possible}
CONSTANTS max_len, max_steps
PROPERTIES max_len:NAT1 &
           max_steps:NAT1
INCLUDES Tape(ALPHA, tape_blank, tape_start, max_len),
         Transition(ALPHA, STATE)
SEES TapeMoves
PROMOTES tape_set, tape_get
VARIABLES state, steps
INVARIANT state:STATE &
          steps:NAT &
          steps <= max_steps
INITIALISATION state := init ||
               steps := 0
OPERATIONS
  add_transition(q1, in, q2, out, move) =
    PRE q1:STATE & in:ALPHA &
        q2:STATE & out:ALPHA & move:MOVE &
        ((q1 = init & in = tape_start) <=> (out = tape_start)) &
        rec(State: q1, Input: in) /: dom(trans)
    THEN
      set_transition(q1, in, q2, out, move)
    END ;

  status <-- step =
    PRE steps < max_steps
    THEN
      IF state = halt
      THEN
        /* We also deal with this case below too, but without this
           instance we won't properly deal with a TM computing the
           identity function, where init = halt */
        status := halted
      ELSE
        IF rec(State: state, Input: cur_sym) /: dom(trans)
        THEN
          status := no_transition_possible
        ELSE
          LET next
          BE
            next = trans(rec(State: state, Input: cur_sym))
          IN
            IF next'Move = Left & pos <= 1
            THEN
              status := segmantation_fault
            ELSIF next'Move = Right & pos >= max_len
            THEN
              status := out_of_memory
            ELSE
              state := next'State ||
              tape_write_then_move(next'Output, next'Move) ||
              steps := steps + 1 ||
              IF next'State = halt
              THEN
                status := halted
              ELSIF steps >= max_steps
              THEN
                status := out_of_time
              ELSE
                status := running
              END
            END
          END
        END
      END
    END
END
