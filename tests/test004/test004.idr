include "simplefile.idr";

%freeze runInterp;

-- test programs

do using (BIND, RETURN) {

  copy : Filepath -> Filepath -> FileSafe TyUnit;
  copy infile outfile = handles 2
           do { fh1 <- OPEN Reading infile;
                fh2 <- OPEN Writing outfile;
                WHILE (do { e <- EOF (handle fh1) ?;
                            return (not e); })
                      (do { str <- GETLINE (handle fh1) ?;
                            PUTLINE (handle fh2) str ?; 
                          });
                CLOSE (handle fh1) ?;
                CLOSE (handle fh2) ?;
              };

  copyLine : Filepath -> Filepath -> FileSafe TyUnit;
  copyLine infile outfile = handles 2
           do { 
                fh1 <- OPEN Reading infile;
                fh2 <- OPEN Writing outfile;
                str <- GETLINE fO openFirst;
                PUTLINE (fS fO) str (openLater openFirst); 
                CLOSE (fS fO) ?;
                CLOSE (fO) ?;
              };
}

copy_1 proof {
        %intro;
        %refine openFirst;
        %qed;
};
copy_2 proof {
        %intro;
        %refine openFirst;
        %qed;
};
copy_3 proof {
        %intro;
        %refine openLater;
        %refine openFirst;
        %qed;
};
copy_4 proof {
        %intro;
        %refine openFirst;
        %qed;
};
copy_5 proof {
        %intro;
        %refine openLater;
        %refine openFirst;
        %qed;
};

copyLine_1 proof {
        %intro;
        %refine openLater;
        %refine openFirst;
        %qed;
};

copyLine_2 proof {
        %intro;
        %refine openFirst;
        %qed;
};

copyLineInt = \inf, outf => ioSnd (interp Empty (copyLine inf outf))
  %spec;
  %freeze copyLine;
  %transform runInterp (interp Empty (copyLine ?inf ?outf)) => copyLineInt ?inf ?outf;

copyInt = \inf, outf => ioSnd (interp Empty (copy inf outf))
  %spec;
  %freeze copy;
  %transform runInterp (interp Empty (copy ?inf ?outf)) => copyInt ?inf ?outf;

do using (BIND, RETURN) {
  copyLots : Filepath -> FileSafe TyUnit;
  copyLots dfile = handles 1
       do { 
            fh1 <- OPEN Reading dfile;
	    WHILE (do { e <- EOF (handle fh1) openFirst;
                        return (not e); })
                  (do { fname <- GETLINE (handle fh1) openFirst;
		        ACTION (putStrLn ("Copying " ++ fname));
		      	IF (not (__strEq fname ""))
			  (call (copy (F fname) (F (fname ++ "~")))) 
			  (RETURN II);
                      });
            CLOSE (handle fh1) openFirst;
          };

}



copyLotsS = \df => ioSnd (interp Empty (copyLots df))
  %spec;
  %freeze copyLots;
  %transform runInterp (interp Empty (copyLots ?df)) => copyLotsS ?df;

main : IO ();
main = copyLotsS (F "lotsdatafile");
