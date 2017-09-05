module CH06.DataStore

import Data.Vect

infixr 5 .+.

data Schema = SString
            | SInt
            | SChar
            | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString   = String
SchemaType SInt      = Int
SchemaType SChar     = Char
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

data DataStore : Type where
  MkData : (schema : Schema)
         -> (size : Nat)
         -> (items : Vect size (SchemaType schema))
         -> DataStore

data Command : Schema -> Type where
  SetSchema : (newschema : Schema)  -> Command schema
  Add  : SchemaType schema -> Command schema
  Get  : Integer -> Command schema
  Size : Command schema
  Quit : Command schema

display : SchemaType schema -> String
display {schema = SString} item             = item
display {schema = SInt} item                = show item
display {schema = SChar} item               = show item
display {schema = (x .+. y)} (iteml, itemr) = display iteml ++ ", " ++ display itemr

parsePrefix : (schema : Schema) -> String -> Maybe (SchemaType schema, String)
parsePrefix SChar input                 = case unpack input of
                                            [x]              => Just (x, "")
                                            (x :: ' ' :: xs) => Just (x, ltrim $ pack xs)
                                            _                => Nothing
parsePrefix SString input               = getQuoted (unpack input)
  where
    getQuoted : List Char -> Maybe (String, String)
    getQuoted ('"' :: xs) =
      case span (/= '"') xs of
        (quoted, '"' :: rest) => Just (pack quoted, ltrim (pack rest))
        _                     => Nothing
    getQuoted _           = Nothing
parsePrefix SInt input                  = case span isDigit input of
                                          ("", _)     => Nothing
                                          (num, rest) => Just (cast num, ltrim rest)
parsePrefix (schemal .+. schemar) input = do
  (lval, inputl) <- parsePrefix schemal input
  (rval, inputr) <- parsePrefix schemar inputl
  pure ((lval, rval), inputr)

parseBySchema : (schema : Schema) -> String -> Maybe (SchemaType schema)
parseBySchema schema input =
  case parsePrefix schema input of
    Just (res, "") => Just res
    _              => Nothing

size : DataStore -> Nat
size (MkData schema' size' items') = size'

schema : DataStore -> Schema
schema (MkData schema' size' items') = schema'

items : (store : DataStore) -> Vect (size store) (SchemaType (schema store))
items (MkData schema' size' items') = items'

addToStore : (store : DataStore) -> SchemaType (schema store) -> DataStore
addToStore (MkData schema' size' store') newitem = MkData schema' _ (addToData store')
  where
    addToData : Vect oldSize (SchemaType schema') -> Vect (S oldSize) (SchemaType schema')
    addToData []        = [newitem]
    addToData (x :: xs) = x :: addToData xs

setSchema : (store : DataStore) -> Schema -> Maybe DataStore
setSchema store schema = case size store of
                           Z => Just (MkData schema _ [])
                           _ => Nothing

parseSchema : List String -> Maybe Schema
parseSchema ("String" :: xs) =
  case xs of
    [] => Just SString
    _  => do
      schema1 <- parseSchema xs
      Just (SString .+. schema1)
parseSchema ("Char" :: xs)   =
  case xs of
    [] => Just SChar
    _  => do
      schema1 <- parseSchema xs
      Just (SChar .+. schema1)
parseSchema ("Int" :: xs)    =
  case xs of
    [] => Just SInt
    _  => do
      schema1 <- parseSchema xs
      Just (SInt .+. schema1)
parseSchema _                = Nothing

parseCommand : (schema : Schema) -> (cmd : String) -> (args : String) -> Maybe (Command schema)
parseCommand schema "schema" rest = SetSchema <$> (parseSchema (words rest))
parseCommand schema "add" val     = Add <$> (parseBySchema schema val)
parseCommand schema "get" val     = if all isDigit (unpack val)
                                    then Nothing
                                    else Just (Get (cast val))
parseCommand schema "quit" ""     = Just Quit
parseCommand schema "size" ""     = Just Size
parseCommand _ _ _                = Nothing

parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = case span (/= ' ') input of
                       (cmd, args) => parseCommand schema cmd (ltrim args)

getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store = let store_items = items store
                     in case integerToFin pos (size store) of
                          Nothing => Just ("Out of range\n", store)
                          Just id => Just ((display $ index id store_items) ++ "\n", store)

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input =
  case parse (schema store) input of
    Nothing                  => Just ("Invalid command\n", store)
    Just (SetSchema schema') => case setSchema store schema' of
                                  Nothing     => Just ("Can't update scema\n", store)
                                  Just store' => Just ("OK\n", store')
    Just (Add item)          => Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
    Just (Get pos)           => getEntry pos store
    Just Size                => Just("Size " ++ show (size store) ++ "\n", store)
    Just Quit                => Nothing

main : IO ()
main = replWith (MkData (SString .+. SString .+. SInt) _ []) "Command: " processInput
