/* For k-tape TMs we want:

MACHINE Tape(..., k)
VARIABLES tapes, positions
INVARIANT tapes : seq1(POSITION) --> seq1(ALPHA) &
          poitionss:seq1(POSITION)
*/

MACHINE Tape(ALPHA,
             tape_blank,
             tape_start,
             max_len)
DEFINITIONS POSITION == (1..max_len)
CONSTRAINTS max_len:NAT1 &
            tape_blank:ALPHA &
            tape_start:ALPHA &
            tape_blank /= tape_start &
            card(ALPHA) > 2
SEES TapeMoves
VARIABLES tape, cur_sym, pos
INVARIANT tape : POSITION --> ALPHA &
          cur_sym:ALPHA &
          pos:POSITION
INITIALISATION tape := POSITION*{tape_blank} <+ {1 |-> tape_start} ||
               cur_sym := tape_start ||
               pos := 1
OPERATIONS
  tape_write_then_move(ss, move) =
    PRE ss:ALPHA &
        ((ss = tape_start) <=> (pos = 1)) &
        move:MOVE &
        ((move = Left)  => (pos > 1)) &
        ((move = Right) => (pos < max_len))
    THEN
      IF move = Left
      THEN
        tape, pos, cur_sym := tape <+ {pos |-> ss}, pos - 1, tape(pos - 1)
      ELSIF move = Right
      THEN
        tape, pos, cur_sym := tape <+ {pos |-> ss}, pos + 1, tape(pos + 1)
      ELSE /* move = None */
        tape, cur_sym := tape <+ {pos |-> ss}, ss
      END
    END ;

  /* useful for reading output */
  ss <-- tape_get(pp) =
    PRE pp:POSITION
    THEN
      ss := tape(pp)
    END ;

  /* useful for setting up input */
  tape_set(pp, ss) =
    PRE pp:POSITION &
        pp > 1 &
        ss:ALPHA &
        ss /= tape_start
    THEN
      tape(pp) := ss
    END
END
