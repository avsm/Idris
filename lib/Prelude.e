%include "string.h"

-- IO

__epic_putStr (x:String) -> Unit =
    foreign Unit "putStr" (x:String)

__epic_readStr () -> String =
    foreign String "readStr" ()

__epic_append (x:String, y:String) -> String =
    foreign String "append" (x:String, y:String)

__epic_newRef () -> Int =
    foreign Int "newRef" ()

__epic_readRef (A:Any, r:Int) -> Any =
    foreign Any "readRef" (r:Int)

__epic_writeRef (A:Any, r:Int, v:Any) -> Unit =
    foreign Unit "writeRef" (r:Int, v:Any)
