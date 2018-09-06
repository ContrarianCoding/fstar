val length: list 'a -> Tot nat
let rec length l =
    match l with
        | [] -> 0
        | _::t -> 1 + length t

val sorted: list int -> Tot bool
let rec sorted l = match l with
  | [] -> true
  | [x] -> true
  | x :: y :: xs -> x <= y && sorted (y :: xs)


val mem: #a:eqtype -> a -> list a -> Tot bool
let rec mem #a x xs =
  match xs with
  | [] -> false
  | hd :: tl -> hd = x || mem x tl

val adding_small_head_stays_sorted: 
    smallhead:int -> sortedlist:list int -> Lemma (requires ((sorted sortedlist) /\ 
                                                            (match sortedlist with | [] -> true | hd::tl -> smallhead <= hd)))
                                                  (ensures (sorted (smallhead::sortedlist)))
let rec adding_small_head_stays_sorted smallhead sortedlist =
    match sortedlist with
        | [] -> ()
        | hd::tl -> adding_small_head_stays_sorted smallhead tl

val mergelists: llst:list int -> rlst:list int -> Tot (rslt:list int)
let rec mergelists llst rlst =
    match (llst, rlst) with
        | (hl::tll, hr::tr) -> if hl <= hr 
                               then hl::(mergelists tll (hr::tr)) 
                               else hr::(mergelists (hl::tll) tr)
        | ([], r) -> r
        | (l, _) -> l

val mergelists_produces_sorted_list: 
    leftlist:list int -> rightlist:list int -> Lemma (requires ((sorted leftlist) /\ (sorted rightlist)))
                                                     (ensures (sorted (mergelists leftlist rightlist)))
let rec mergelists_produces_sorted_list leftlist rightlist =
    match leftlist, rightlist with
        | hdl::tll, hdr::tlr -> if hdl <= hdr 
        then mergelists_produces_sorted_list tll (hdr::tlr)
        else mergelists_produces_sorted_list (hdl::tll) tlr
        | _, _ -> ()

val mergestep: lstlst:list (list int) -> Tot (rslt:list (list int){(length rslt <= length lstlst)})
let rec mergestep lstlst =
    match lstlst with
        | [] -> []
        | [x] -> [x]
        | h::n::t -> (mergelists h n)::mergestep t 

val mergestep_keeps_members_sorted: lstlst: list (list int) -> Lemma (requires (forall i. mem i lstlst ==> sorted i))
                                                                   (ensures (forall j. mem j (mergestep lstlst) ==> sorted j))
let rec mergestep_keeps_members_sorted lstlst =
    match lstlst with
        | [] -> ()
        | [x] -> ()
        | h::n::t -> (mergelists_produces_sorted_list h n);(mergestep_keeps_members_sorted t)                                                           

val mergerec: lstlst:(list (list int)) -> Tot (rslt:list int)(decreases (length lstlst))
let rec mergerec lstlst =
    match lstlst with
        | [] -> []
        | [x] -> x
        | _ -> mergerec (mergestep lstlst)

val mergerec_sorts: lstlst: list (list int) -> Lemma (requires (forall i. mem i lstlst ==> sorted i))
                                                     (ensures (sorted (mergerec lstlst)))(decreases (length lstlst))
let rec mergerec_sorts lstlst =
    match lstlst with
        | [] -> ()
        | [x] -> ()
        | h::n::t -> (mergestep_keeps_members_sorted lstlst);(mergerec_sorts (mergestep lstlst))


val modulize: list int -> Tot (modules:list (list int){forall i. mem i modules ==> sorted i})
let rec modulize lst = 
    match lst with
        | [] -> []
        | h::t -> [h]::modulize t

val mergesort: lst:list int -> Tot (rslt:list int)

let mergesort lst = mergerec (modulize lst)


val mergesort_sorts: anylist:list int -> Lemma (requires (True))
                                            (ensures (sorted (mergesort anylist)))
let rec mergesort_sorts anylist =
    match anylist with
        | [] -> ()
        | [x] -> ()
        | h::n::t -> (mergerec_sorts (modulize anylist))

