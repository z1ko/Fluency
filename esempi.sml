
print (
    "===================== SCELTA NON DETERMINISTICA =====================\n" ^
    "La seguente espressione assegna alla variabile x un valore in modo non deterministico\n\n"
);

digest (
    Choice (
        Choice (
            Assign ("x", Op(Integer 1, Add, Deref "x")), 
            Choice(
                Assign ("x", Integer 2),
                Assign ("x", Integer 3)
            )
        ), 
        Assign ("x", Op(Integer 9, Add, Integer 1))
    ), 
    SOME [("x", 0)]
);

print (
    "===================== PARALLELO =====================================\n" ^ 
    "Il valore della variabile x dipende dall'ordine di esecuzione\n\n"
);

digest (
    Par (
        Assign ("x", Op(Deref "x", Add, Integer 1)), 
        Assign ("x", Op(Deref "x", Add, Integer 2))
    ), 
    SOME [("x", 0)]
);

print (
    "===================== AWAIT TRUE ===================================\n" ^
    "In questo esempio viene eseguita solo una wait\n\n"
);

digest (
    Par (
        Await (
            Boolean false,  
            Assign ("y", Op(Deref "x", Add, Integer 1))
        ), 
        Await (
            Boolean true,
            Seq (
                Assign ("x", Integer 1), 
                Assign ("y", Integer 1)
            )
        )
    ), 
    SOME [("x", 0), ("y", 0)]
);

print (
    "===================== COMPLESSO ===================================\n" ^
    "Combinazione parallela fra una await e una scelta non deterministica\n\n"
);

digest (
    Par (
        Await (
            Boolean true,
            Seq (
                Assign ("x", Op (Deref "y", Add, Integer 1)),
                Assign ("y", Op (Deref "x", Add, Integer 1))
            )
        ),
        Choice (
            Choice (
                Assign("x", Integer 2),
                Assign("y", Integer 2)
            ),
            Assign ("x", Op (Deref "y", Add, Integer 5))
        )
    ),
    SOME [("x", 0), ("y", 0)]
);

quit();

