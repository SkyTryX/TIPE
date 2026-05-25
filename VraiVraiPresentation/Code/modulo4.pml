/* Etats: 0=00, 1=01, 2=10, 3=11 */
bool phi1 = false, phi2 = false, r = true;
mtype = {S0, S1, S2, S3};
mtype state = S0;                             

proctype System() {
  do
  :: atomic {
       if
       :: state == S0 -> phi1 = false; phi2 = false; r = true;
       :: state == S1 -> phi1 = false; phi2 = true;  r = false;
       :: state == S2 -> phi1 = true;  phi2 = false; r = false;
       :: state == S3 -> phi1 = true;  phi2 = true;  r = false;
       fi;
     }
  :: atomic { state == S0 -> state = S1 }
  :: atomic { state == S1 -> state = S2 }
  :: atomic { state == S2 -> state = S3 }
  :: atomic { state == S3 -> state = S0 }
  od
}

/* lance le proctype (ne sert plus à initialiser les valeurs) */
init {
  run System();
}

ltl p1 { [] ( phi2 <-> X(!phi2) ) }
ltl p2 { [] ( phi2 <-> (phi1 <-> X(!phi1)) ) }
ltl p3 { [] ( r <-> !(phi1 || phi2) ) }

    /* COMMANDE A EXECUTER
    spin -a modulo4.pml
    gcc -O2 -o pan pan.c
    ./pan -a -N p1/p2/p3
    */