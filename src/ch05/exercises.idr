module CH05

import System

ask : String -> IO String
ask prompt = do
  putStr prompt
  getLine

printLonger : IO ()
printLonger = do
  line1 <- ask "First string: "
  line2 <- ask "Second string: "
  print (max (length line1) (length line2))

guess : (target : Nat) -> (guesses : Nat) -> IO ()
guess target guesses = do
  guessed <- cast <$> ask ("guess(" ++ show guesses ++ "): ")
  case compare guessed target of
    EQ => putStrLn "yay!"
    LT => do
      putStrLn "too low"
      guess target (succ guesses)
    GT => do
      putStrLn "to high"
      guess target (succ guesses)

xRepl : String -> (String -> String) -> IO ()
xRepl prompt f = do
  putStr prompt
  getLine >>= putStr . f
  xRepl prompt f

xReplWith : a -> String -> (a -> String -> Maybe (String, a)) -> IO ()
xReplWith st prompt f = do
  putStr prompt
  line <- getLine
  case f st line of
    Nothing => pure ()
    Just (output, st') => do
      putStr output
      xReplWith st' prompt f

testReplWith : IO ()
testReplWith =
  xReplWith 0 "foobar: " foobar
  where
    foobar : Int -> String -> Maybe (String, Int)
    foobar s line = Just (line ++ (show s), s+1)

main : IO ()
main = do
  target <- cast <$> time
  guess (1 + mod target 100) 0
