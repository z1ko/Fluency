
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

    (* Aggiorna un valore dello store *)
    fun update store (loc, value) = update_iterator [] store (loc, value)

    (* Aggiunge una nuova locazione *)
    fun insert store (loc, value) = ((loc, value)::store)

    (* Controlla una singola coppia dello store e possibilmente la rimuove*)
    fun remove_iterator front [] loc = NONE
      | remove_iterator front ((loc', value')::tail) loc =
            if loc' = loc then SOME (front @ tail)
            else remove_iterator ((loc', value')::front) tail loc

    (* Rimuove un valore dallo store*)
    fun remove store loc = remove_iterator [] store loc

end

(* Store.read (Option.getOpt ((Store.update (Store.insert [] ("x", 5)) ("x", 0)), [])) "x"; *)