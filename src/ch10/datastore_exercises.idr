module datastore_exercises

import DataStore

testStore : DataStore (SString .+. (SString .+. SInt))
testStore =
  addToStore ("Mercury", "Mariner 10", 1974) $
  addToStore ("Venus", "Venera", 1961) $
  addToStore ("Uranus", "Voyager 2", 1986) $
  addToStore ("Pluto", "New Horizons", 2015) $
  empty

getValues : DataStore (SString .+. val_schema) -> List (SchemaType val_schema)
getValues store with (storeView store)
  getValues empty | SNil = []
  getValues (addToStore (_, value) store) | SAdd store' = value :: getValues store | store'
