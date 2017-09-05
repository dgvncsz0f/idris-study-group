module CH06.Printf

import Data.Vect

data Format = Number Format
            | Chr Format
            | Str Format
            | Lit String Format
            | Dbl Format
            | End

PrintfType : Format -> Type
PrintfType (Number fmt)  = Int -> PrintfType fmt
PrintfType (Chr fmt)     = Char -> PrintfType fmt
PrintfType (Str fmt)     = String -> PrintfType fmt
PrintfType (Dbl fmt)     = Double -> PrintfType fmt
PrintfType (Lit str fmt) = PrintfType fmt
PrintfType End           = String

printfFmt : (fmt : Format) -> (acc : String) -> PrintfType fmt
printfFmt (Number fmt) acc  = \i => printfFmt fmt (acc ++ show i)
printfFmt (Str fmt) acc     = \s => printfFmt fmt (acc ++ s)
printfFmt (Lit lit fmt) acc = printfFmt fmt (acc ++ lit)
printfFmt (Chr fmt) acc     = \c => printfFmt fmt (acc ++ strCons c "")
printfFmt (Dbl fmt) acc     = \n => printfFmt fmt (acc ++ show n)
printfFmt End acc           = acc

toFormat : (xs : List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: chars) = Number (toFormat chars)
toFormat ('%' :: 's' :: chars) = Str (toFormat chars)
toFormat ('%' :: 'c' :: chars) = Chr (toFormat chars)
toFormat ('%' :: 'f' :: chars) = Dbl (toFormat chars)
-- toFormat ('%' :: chars)        = Lit "%" (toFormat chars)
toFormat (c :: chars)          = case toFormat chars of
                                   Lit lit chars' => Lit (strCons c lit) chars'
                                   fmt => Lit (strCons c "") fmt

printf : (fmt : String) -> PrintfType (toFormat (unpack fmt))
printf fmt = printfFmt _ ""
