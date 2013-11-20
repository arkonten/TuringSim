MACHINE Turing(ALPHA,
               blank,
               start,
               STATE,
               init,
               halt)
CONSTRAINTS card(ALPHA) > 2 &
            blank:ALPHA &
            start:ALPHA &
            blank /= start &
            init:STATE &
            halt:STATE
SETS STATUS = {halted,
               running,
               error}
VARIABLES state,
          tape,
          pos,
          trans,
          status
INVARIANT state:STATE &
          tape:seq1(ALPHA) &
          first(tape) = start &
          (!cell.(cell:ran(tail(tape)) => cell /= start)) &
          pos:NAT &
          trans : struct(State: STATE, Tape: seq1(ALPHA), Pos: NAT) +->
                  struct(State: STATE, Tape: seq1(ALPHA), Pos: NAT) &
          !(ss,tt,pp).((ss:STATE &
                        tt:seq1(ALPHA) &
                        pp:NAT &
                        rec(State: ss, Tape: tt, Pos: pp):dom(trans))
                          => ss /= halt) &
          status:STATUS

INITIALISATION state := init ||
               tape := [start] ||
               pos := 1 ||
               trans := {} ||
               status := running
OPERATIONS
  add_transition(s1, t1, p1, s2, t2, p2) =
    PRE s1:STATE &
        t1:seq1(ALPHA) &
        p1:NAT &
        s2:STATE &
        t2:seq1(ALPHA) &
        p2:NAT &
        s1 /= halt &
        rec(State: s1, Tape: t1, Pos: p1) /: dom(trans) &
        ((first(t1) = start) <=> (first(t2) = start)) &
        (!cell.(cell:ran(tail(t1)) => cell /= start)) &
        (!cell.(cell:ran(tail(t2)) => cell /= start))
    THEN
      trans := trans <+ { rec(State: s1, Tape: t1, Pos: p1) |->
                          rec(State: s2, Tape: t2, Pos: p2) }
    END ;

  push_input(ss) =
    PRE ss:ALPHA &
        ss /= start
    THEN
      tape := tape <- ss
    END ;

  run =
    PRE state = init &
        status = running &
        rec(State: state, Tape: tape, Pos: pos):dom(trans)
    THEN
      LET final
      BE
        final = closure(trans)(rec(State: state, Tape: tape, Pos: pos))
      IN
        state := final'State ||
        tape := final'Tape ||
        pos := final'Pos ||
        IF final'State = halt
        THEN
             status := halted
        ELSE
             status := error
        END
      END
    END
END
