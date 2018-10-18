%default total

-- Hangman refactored ----------------------------------------------------------

-- The version appearing in Chapter 14 of Type-Driven Development with Idris is
-- hard to follow. Why the two different forms of game state ("abstract" and
-- "concrete")? What does the abstract form abstract over? Where is the actual
-- proof that the state machine can enter only legal states? Does the use of
-- corecursion actually do anything to clarify the code, or is it just messy
-- boilerplate?

-- Here's a version of Hangman with just one form of game state and no
-- corecursion. It includes an explicit proof that any state reached by making a
-- move in the game is legal (results from permissible transitions from a valid
-- start state).

-- I've changed the order of parameters to the datatype describing state
-- transitions so that the current state precedes the type of input expected for
-- the transition. In a generalized state machine, the latter might depend on
-- the former. For example, although Hangman lets you play any letter at any
-- point in the game, Tic-Tac-Toe requires that you play only on a space that
-- has not yet been filled -- meaning that the type of input expected for the
-- transition would be a pair of coordinates along with a proof that the
-- specified location is unoccupied in the current state.

-- Some of the declarations below could be generalized over an arbitrary state
-- machine paired with a notion of legal starting and ending states: namely
-- Legal, go, and gameLoop. move would be hard to generalize; it would require
-- somehow decoupling the user interaction for a game from the game rules,
-- although you can imagine rephrasing it in terms of a GameInterface type that
-- could be implemented, for example, both in terms of terminal interaction and
-- some sort of GUI.

-- Game states and transitions -------------------------------------------------

||| Maximum incorrect guesses allowed in a game
MaxGuesses: Nat
MaxGuesses = 6

||| Game states
data St: Type where
  NotPlaying: St
  Playing: (word: String) -> (remChars: List Char) -> (remGuesses: Nat) -> St

||| Legal game state transitions, where inputType is the type of input required
||| (from someplace outside the state machine proper, like user input) in order
||| to complete a transition from currentState by applying transition
data Tr:
    (currentState: St) -> (inputType: Type) -> (transition: inputType -> St) ->
    Type where
  NewGame:   -- if you're not playing, you can start, with all letters unguessed
    Tr NotPlaying String
      (\word => (Playing word (nub $ unpack $ trim word) MaxGuesses))
  Guess:            -- guess, as long as there are letters and guesses remaining
    {remChars: List Char} -> {auto haveRemChars: remChars = _ :: _} ->
    {remGuesses: Nat} -> {auto haveRemGuesses: remGuesses = S p} ->
    Tr (Playing word remChars remGuesses) Char
      (\ch =>
        if elem ch remChars
          then Playing word (delete ch remChars) remGuesses
          else Playing word remChars p)
  Won:        -- you win if you have unused guesses but no letters left to guess
    Tr (Playing _ Nil (S _)) () (const NotPlaying)
  Lost:  -- you lose if you have no guesses left but there are unguessed letters
    Tr (Playing _ (_ :: _) Z) () (const NotPlaying)
  (>>=):             -- turns a transition expecting an a into one expecting a b
    Tr st0 a trbyA ->
    ((input: a) -> Tr (trbyA input) b trbyB) ->
    Tr st0 b trbyB
  -- There is no Pure! A Pure constructor that takes a transition function as
  -- a parameter would let you construct an arbitrary state transition, but
  -- the whole point is that the above list of possible transitions is
  -- exhaustive
  
||| A legal state is one reached from NotPlaying by zero or more transitions
data Legal: St -> Type where
  NotPlayingLegal:
    Legal NotPlaying
  TransitionLegal:
    Legal start -> Tr start inTy trFun -> (input: inTy) -> Legal (trFun input)

-- Compiletime tests of the transitions (by abuse of do notation) --------------

||| Goes from NotPlaying to NotPlaying by guessing the word "cat"
partial
SampleWinningGame: Tr NotPlaying () (const NotPlaying)
SampleWinningGame = do
  "cat" <- NewGame
  'c' <- Guess
  'a' <- Guess
  't' <- Guess
  Won
  
||| Goes from NotPlaying to NotPlaying by failing to guess the word "dog"
partial
SampleLosingGame: Tr NotPlaying () (const NotPlaying)
SampleLosingGame = do
  "dog" <- NewGame
  'c' <- Guess
  'a' <- Guess
  't' <- Guess
  'w' <- Guess  
  'o' <- Guess  -- got this one right!
  'l' <- Guess
  'f' <- Guess
  Lost
  
-- State utilities -------------------------------------------------------------

||| Makes a state transition from a legal state to a legal state
go: (st ** Legal st) -> Tr st inTy trFun -> (input: inTy) -> (st' ** Legal st')
go {trFun} (st ** stOK) tr input =
  (trFun input ** TransitionLegal stOK tr input)

||| Describes a state
showState: St -> String
showState NotPlaying = "Not playing"
showState (Playing word remChars remGuesses) =
  pack (map hideMissing (unpack word)) ++ "    " ++ show remGuesses ++
    " guesses left."
  where
  hideMissing: Char -> Char
  hideMissing c = if c `elem` remChars then '-' else c

-- Playing the game ------------------------------------------------------------

||| Makes a legal state transition from st to next based on input from IO
move: (st ** Legal st) -> IO (next ** Legal next)
move (st ** stOK) with (st)
  move (st ** stOK) | NotPlaying = do
    putStrLn "Let's play Hangman!"
    putStr "What word would you like to guess? "
    word <- getLine
    putStrLn "Make sure to forget your word while you're guessing. No cheating!"
    pure (go (st ** stOK) NewGame word)
  move (st ** stOK) | (Playing word remChars remGuesses) with (remChars)
    move (st ** stOK) | (Playing word remChars remGuesses) | []
        with (remGuesses)
      move (st ** stOK) | (Playing word remChars remGuesses) | [] | Z = do
        putStrLn ("Illegal state: " ++ showState st)
        pure (NotPlaying ** NotPlayingLegal)
      move (st ** stOK) | (Playing word remChars remGuesses) | [] | S p = do
        putStrLn (showState st)
        putStrLn "You win!"
        pure (go (st ** stOK) Won ())
    move (st ** stOK) | (Playing word remChars remGuesses) | (x :: xs)
        with (remGuesses)
      move (st ** stOK) | (Playing word remChars remGuesses) | (x :: xs) | Z =
        do
        putStrLn (showState st)
        putStrLn "You lost. Next time, try cheating!"
        pure (go (st ** stOK) Lost ())
      move (st ** stOK) | (Playing word remChars remGuesses) | (x :: xs) | S p =
        do
        putStrLn (showState st)
        putStr "Guess a letter: "
        chs <- getLine
        case unpack chs of
          Nil => do
            putStrLn
              "Empty string! I'll pretend you guessed the space character."
            pure (go (st ** stOK) Guess ' ')
          (ch :: _) => do
            putStrLn ("You guessed " ++ show ch)
            pure (go (st ** stOK) Guess ch)

partial
gameLoop: (st ** Legal st) -> IO ()
gameLoop (st ** stOK) = do
  next <- move (st ** stOK)
  case next of
    (NotPlaying ** _) => pure ()
    _ => gameLoop next

partial
main: IO ()
main = gameLoop (NotPlaying ** NotPlayingLegal)
