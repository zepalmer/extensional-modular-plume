module Utils.PpUtils where

ppConcatSepDelim :: String -> String -> String -> (a -> String) -> [a] -> String
ppConcatSepDelim start stop sep ppItem items = 
    start ++
    ppConcatSep sep ppItem items ++
    stop

ppConcatSep :: String -> (a -> String) -> [a] -> String
ppConcatSep sep ppItem items =
    let loop entities = 
            case entities of
                [] -> ""
                entity : [] -> ppItem entity
                entity : entities' -> ppItem entity ++ sep ++ loop entities'
    in loop items