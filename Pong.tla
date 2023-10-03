------------------------ MODULE Pong ------------------------
EXTENDS Integers, Sequences

CONSTANTS MaxX, MaxY, WinningScore, BallSpeed, PaddleSpeed, InitialBallX, InitialBallY

VARIABLES ball, ballDirection, player1, player2, score1, score2, gameOver

(* Custom absolute value operator *)
Abs(x) == IF x < 0 THEN -x ELSE x

(* Initial state *)
Init ==
    /\ ball = <<InitialBallX, InitialBallY>>
    /\ ballDirection = <<1, 1>> 
    /\ player1 = MaxY \div 2
    /\ player2 = MaxY \div 2
    /\ score1 = 0
    /\ score2 = 0
    /\ gameOver = 0   \* Game is not over at the beginning

(* Move Paddle Action *)
MovePaddle1(newPosition) ==
    /\ player1' = IF Abs(newPosition - player1) <= PaddleSpeed
                  THEN IF newPosition < 0 THEN 0
                       ELSE IF newPosition > MaxY THEN MaxY
                            ELSE newPosition
                  ELSE player1 + PaddleSpeed * ((newPosition - player1) \div Abs(newPosition - player1))
    /\ UNCHANGED <<ball, ballDirection, player2, score1, score2, gameOver>>

MovePaddle2(newPosition) ==
    /\ player2' = IF Abs(newPosition - player2) <= PaddleSpeed
                  THEN IF newPosition < 0 THEN 0
                       ELSE IF newPosition > MaxY THEN MaxY
                            ELSE newPosition
                  ELSE player2 + PaddleSpeed * ((newPosition - player2) \div Abs(newPosition - player2))
    /\ UNCHANGED <<ball, ballDirection, player1, score1, score2, gameOver>>

(* Update Ball Position *)
UpdateBallPosition ==
    ball' = <<ball[1] + ballDirection[1] * BallSpeed, ball[2] + ballDirection[2] * BallSpeed>>

(* Check Ball-Paddle Collision and adjust ball position if necessary *)
CheckPaddleCollision ==
    /\ IF (ball[1] <= 1 /\ ball[2] >= player1 /\ ball[2] <= player1 + 3) 
       THEN /\ ballDirection' = <<-ballDirection[1], ballDirection[2]>>
            /\ ball'[1] = 2  \* Move ball away from the edge
       ELSE IF (ball[1] >= MaxX - 1 /\ ball[2] >= player2 /\ ball[2] <= player2 + 3)
            THEN /\ ballDirection' = <<-ballDirection[1], ballDirection[2]>>
                 /\ ball'[1] = MaxX - 2  \* Move ball away from the edge
            ELSE UNCHANGED <<ballDirection>>

(* Check and Update Score *)
CheckScore ==
    /\ IF ball'[1] <= 0
         THEN /\ score2' = score2 + 1
              /\ ball' = <<InitialBallX, InitialBallY>>
              /\ ballDirection' = <<1, 1>>
              /\ IF score2' >= WinningScore THEN gameOver' = 1 ELSE UNCHANGED gameOver
       ELSE IF ball'[1] >= MaxX
         THEN /\ score1' = score1 + 1
              /\ ball' = <<InitialBallX, InitialBallY>>
              /\ ballDirection' = <<1, 1>>
              /\ IF score1' >= WinningScore THEN gameOver' = 1 ELSE UNCHANGED gameOver
         ELSE UNCHANGED <<score1, score2, ballDirection, gameOver>>

(* Move Ball Action *)
MoveBall ==
    /\ UpdateBallPosition
    /\ CheckPaddleCollision
    /\ CheckScore
    /\ UNCHANGED <<player1, player2>>

(* Next State Action *)
Next ==
    IF gameOver = 0
    THEN
        /\ \/ \E newPosition \in 0..MaxY: MovePaddle1(newPosition)
           \/ \E newPosition \in 0..MaxY: MovePaddle2(newPosition)
           \/ MoveBall 
    ELSE UNCHANGED <<ball, ballDirection, player1, player2, score1, score2, gameOver>>


(* Invariants *)
TypeOK ==
    /\ ball[1] \in 0..MaxX
    /\ ball[2] \in 0..MaxY
    /\ ballDirection[1] \in {-1,1}
    /\ ballDirection[2] \in {-1,1}
    /\ player1 \in 0..MaxY
    /\ player2 \in 0..MaxY
    /\ score1 \in Nat
    /\ score2 \in Nat
    /\ gameOver \in {0,1}  \* gameOver is either 0 (game ongoing) or 1 (game over)

(* Specification *)
Spec ==
    Init /\ [][Next]_<<ball, ballDirection, player1, player2, score1, score2, gameOver>>

=============================================================================
