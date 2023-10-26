(* MP1 2023/2024 - dpll.ml *)

open List

(* fonctions utilitaires *)
(* ----------------------------------------------------------- *)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien ajouter au résultat.
   Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []

(* print_modele : int list option -> unit
   affichage du résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"

(* ensembles de clauses de test *)
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let coloriage = [
  [1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];
  [19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];
  [-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];
  [-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];
  [-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];
  [-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];
  [-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];
  [-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];
  [-14;-17];[-15;-18]]

(* ----------------------------------------------------------- *)

(* simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral l à vrai *)
let simplifie l clauses =
  filter_map ( fun clause -> 
    if List.mem l clause then
      None 
    else
      Some ( List.filter ( fun litteral -> litteral <> -l) clause)  
    ) clauses
    (*On verifie ici si "l" est dans la clause
      Retirer les Clauses Satisfaites : 
      Si l est présent dans une clause, cette clause est déjà satisfaite et est retirée de la liste.
      Retirer les Littéraux Faux : 
      Si -l (l'opposé de l) est présent dans une clause, il est retiré car il est faux.   

      Puis on utilise Some pour rajouter les clauses apres avoir filtree dans la nouvelle liste "clauses"
    *) 

(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
(* cette fonction ne doit pas être modifiée, sauf si vous changez 
   le type de la fonction simplifie *)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* la clause vide n'est jamais satisfiable *)
  if mem [] clauses then None else
  (* branchement *) 
  let l = hd (hd clauses) in
  let branche = solveur_split (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche

(* tests *)
(* let () = print_modele (solveur_split systeme []) *)
(* let () = print_modele (solveur_split coloriage []) *)

(* solveur dpll récursif *)
(* ----------------------------------------------------------- *)

(* pur : int list list -> int
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon, lève une exception `Failure "pas de littéral pur"' *)
let pur clauses =
    let tous_litteraux = 
      (* aplatie la liste des clauses en une seule liste
         [[1,2,3][2,3]]->[1,2,3,2,3] *)
      List.flatten clauses in
  let rec trouver_litteral_pur litteraux =
    match litteraux with
    | [] -> raise (Failure "pas de littéral pur")
    | hd :: tl -> 
      (* on check si -hd est present dans la liste 
         Si -hd est present on check le reste de la liste *)
        if List.mem (-hd) tous_litteraux then 
          trouver_litteral_pur tl 
        else 
          (* si -hd est pas la, hd est donc pur *)
          hd
  in 
  (* on reutilise trouver_litteral_pur avec une list dj triee
     sans doublons
     cette ligne est pour but de trier et supprimer les doublons 
     car un pur pourrait apparaitre plusieures fois dans la liste
     en supprimant les doublons, on reduit la taille
     et accelerer le processus *)
  trouver_litteral_pur (List.sort_uniq compare tous_litteraux)

(* unitaire : int list list -> int
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon, lève une exception `Not_found' *)
let rec unitaire clauses =
  match clauses with
    | [] -> raise Not_found (*lève une exception Not_found*)
    | [x] :: tl -> x (*on renvoie le littéral si clause unitaire*)
    | hd :: tl -> unitaire tl (*on passe à la clause suivante*)
 
(* solveur_dpll_rec : int list list -> int list -> int list option 
   
 + but est de déterminer s'il existe une affectation des variables 
   booléennes qui rend toutes les clauses vraies.*)
let rec solveur_dpll_rec clauses interpretation =
  (* à compléter *)
  None


(* tests *)
(* ----------------------------------------------------------- *)
(* let () = print_modele (solveur_dpll_rec systeme []) *)
(* let () = print_modele (solveur_dpll_rec coloriage []) *)

let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses [])

    