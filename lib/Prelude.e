%include "string.h"

-- IO

%inline __epic_id (x:Any) -> Any = x

%inline __epic_putStr (x:String) -> Unit =
    foreign Unit "putStr" (x:String)

__epic_readStr () -> String =
    foreign String "readStr" ()

__epic_append (x:String, y:String) -> String =
    foreign String "append" (x:String, y:String)

__epic_strlen (x:String) -> Int =
    foreign Int "strlen" (x:String)

__epic_strhead (x:String) -> Int =
    foreign Int "strHead" (x:String)

__epic_strtail (x:String) -> String =
    foreign String "strTail" (x:String)

__epic_strcons (h:Int, x:String) -> String =
    foreign String "strCons" (h:Int, x:String)

__epic_streq (x:String, y:String) -> Data =
    foreign Int "streq" (x:String, y:String)

__epic_strrev (x:String) -> String =
    foreign String "strrev" (x:String)

%inline __epic_chareq (x:Int, y:Int) -> Data = x==y

%inline __epic_strlt (x:String, y:String) -> Data =
    foreign Int "strlt" (x:String, y:String)

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
   lazy foreign Unit "doFork" (f:Fun)

__epic_within (a:Any, i:Int, f:Fun, fail:Fun) -> Unit =
   lazy foreign Unit "doWithin" (i:Int, f:Fun, fail:Fun)

%inline __epic_bool (x:Int) -> Data =
   if (x==0) then (Con 1 ()) else (Con 0 ())

__epic_toInt (x:String) -> Int = 
   foreign Int "strToInt" (x:String)

__epic_toString (x:Int) -> String = 
   foreign String "intToStr" (x:Int)

__epic_native (x:Fun) -> Ptr =
   foreign Ptr "getNative" (x:Fun)

