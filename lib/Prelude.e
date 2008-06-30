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

__epic_newLock (l:Int) -> Int =
   foreign Int "newLock" (l:Int)

__epic_doLock (l:Int) -> Unit =
   foreign Unit "doLock" (l:Int)

__epic_doUnlock (l:Int) -> Unit =
   foreign Unit "doUnlock" (l:Int)

__epic_fork (a:Any, f:Fun) -> Unit =
   foreign Unit "doFork" (f:Fun)

