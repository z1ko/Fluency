
structure Store = struct

    (* Ottiene valore di una locazione nello store se presente, NB: solo interi *)
    fun read [] loc = NONE
      | read ((loc_name, value)::store) loc = 
          if loc_name = loc then SOME value 
          else read store loc

    (* Controlla una singola coppia dello store *)
    fun update_iterator front [] (loc, value) = NONE
      | update_iterator front ((pair_loc, pair_value)::tail) (loc, value) =
          if pair_loc = loc then SOME (front @ (loc, value)::tail) (* Restituisce lo store aggiornato *)
          else update_iterator ((pair_loc, pair_value)::front) tail (loc, value) (* Controlla tupla successiva *)

    (* Aggiorna un valore dello store, ritorna una copia *)
    fun update store (loc, value) = update_iterator [] store (loc, value)

end