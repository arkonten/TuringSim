/* For k-tape TMs we want:

MACHINE Transition(..., k)
SETS ALPHAK := seq1(ALPHA) ;
     MOVEK  := seq1(MOVE)
PROPERTIES card(ALPHAK) = k & card(MOVE) = k
INVARIANT trans : struct(State:  STATE,
                         Input:  ALPHAK) +->
                  struct(State:  STATE,
                         Output: ALPHAK,
                         Move:   MOVEK)
*/

MACHINE Transition(ALPHA, STATE)
SEES TapeMoves
VARIABLES trans
INVARIANT trans : struct(State: STATE,
                         Input: ALPHA) +->
                  struct(State:  STATE,
                         Output: ALPHA,
                         Move:   MOVE)
INITIALISATION trans := {}
OPERATIONS
  set_transition(q1, in, q2, out, move) =
    PRE q1:STATE & in:ALPHA &
        q2:STATE & out:ALPHA & move:MOVE
    THEN
      trans(rec(State: q1, Input: in)) :=
        rec(State: q2, Output: out, Move: move)
    END
END
