module Exercices

import Data.Vect

ask : String -> IO String
ask prompt = do
  putStr prompt
  getLine

readToBlank : IO (List String)
readToBlank = do
  line <- ask "input (empty line to finish): "
  if line == ""
  then pure []
  else (line ::) <$> readToBlank

readAndSave : IO ()
readAndSave = do
  contents <- readToBlank
  filepath <- ask "filename: "
  Right () <- writeFile filepath (concat $ intersperse "\n" contents)
    | Left err => putStrLn ("ERROR: " ++ show err)
  pure ()

readVect : File -> IO (Either FileError (n ** Vect n String))
readVect fh = do
  eof <- fEOF fh
  if eof
  then pure (Right (_ ** []))
  else do
    Right x <- fGetLine fh
      | Left error => pure (Left error)
    Right (_ ** xs) <- readVect fh
      | Left error => pure (Left error)
    pure (Right (_ ** (trim x) :: xs))

readVectFile : (filepath : String) -> IO (n ** Vect n String)
readVectFile filepath = do
  Right fh <- openFile filepath Read
  Right ans <- readVect fh
  closeFile fh
  pure ans
