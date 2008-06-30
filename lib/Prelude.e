%include "string.h"

-- IO

__epic_putStr (x:String) -> Unit =
    foreign Unit "putStr" (x:String)

__epic_readStr () -> String =
    foreign String "readStr" ()

__epic_append (x:String, y:String) -> String =
    foreign String "append" (x:String, y:String)

