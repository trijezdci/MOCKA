(*!m2pim+mocka*)

(* ------------------------------------------------------------------------ *
 * MOCKA Modula-2 Compiler System, Version 1807                             *
 *                                                                          *
 * Copyright (C) 1988-2000 by                                               *
 *  GMD Gesellschaft fuer Mathematik und Datenverarbeitung,                 *
 *  Ehemalige GMD Forschungsstelle an der Uni Karlsruhe;                    *
 *  [EN] German National Research Center for Computer Science,              *
 *  Former GMD Research Lab at the University of Karlsruhe.                 *
 *                                                                          *
 * Copyright (C) 2001-2018 by                                               *
 *  Fraunhofer-Gesellschaft zur Foerderung der angewandten Forschung;       *
 *  [EN] Fraunhofer Society for the Advancement of Applied Research.        *
 * ------------------------------------------------------------------------ *)

IMPLEMENTATION MODULE GcgStorage;
                       
  FROM SYSTEM IMPORT ADDRESS;                    
  FROM MemPools IMPORT MemPool, NewPool, PoolAllocate, KillPool;

  VAR
    pool: MemPool;

  PROCEDURE ALLOCATE (VAR ptr : ADDRESS; size : LONGCARD);
  BEGIN
    PoolAllocate(pool, ptr, size);
  END ALLOCATE;

  PROCEDURE InitGcgStorage;
  BEGIN
    KillPool(pool);
    NewPool(pool);
  END InitGcgStorage;

BEGIN
  NewPool(pool);
END GcgStorage.
