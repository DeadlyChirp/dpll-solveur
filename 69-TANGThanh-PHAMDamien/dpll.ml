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
(* let () = print_modele (solveur_split systeme []) 
let () = print_modele (solveur_split coloriage []) *)

(* solveur dpll récursif *)
(* ----------------------------------------------------------- *)

(* pur : int list list -> int
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon, lève une exception `Failure "pas de littéral pur"' *)
    let pur clauses =
      let rec auxiliaire clauses accumulateur =
        match clauses with
        | [] -> raise (Failure "pas de littéral pur")
        | clause_courante::clauses_restantes ->
          let negatifs, positifs = List.partition (fun l -> l < 0) clause_courante in
          let negatifs = List.map abs negatifs in
          let nouvel_accumulateur = List.fold_left (fun acc l -> if List.mem l acc || List.mem (-l) acc then acc else l::acc) accumulateur (negatifs @ positifs) in
          auxiliaire clauses_restantes nouvel_accumulateur
      in auxiliaire clauses []
    (* La fonction pur cherche un littéral pur dans une liste de clauses, 
       où une clause est une liste de littéraux représentés par des entiers (positifs ou négatifs). 
       Pour chaque clause, elle sépare les littéraux positifs et négatifs, convertit les négatifs en positifs, 
       et les ajoute à un accumulateur sauf s'ils sont déjà présents avec l'opposé. 
       Si elle atteint la fin de la liste sans trouver de littéral pur, elle lève une exception. 
       L'accumulateur sert à garder une trace des littéraux déjà vus. 
       Le but est de trouver un littéral qui apparaît toujours avec le même signe dans toutes les clauses. *)

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
          if clauses = [] then Some interpretation else
          if mem [] clauses then None else
            try 
              let unit_clause = unitaire clauses in solveur_dpll_rec (simplifie unit_clause clauses) (unit_clause::interpretation)
            with Not_found ->
              try 
                let pure_literal = pur clauses in solveur_dpll_rec (simplifie pure_literal clauses) (pure_literal::interpretation)
              with Failure _ ->
                let literals = List.flatten clauses in
                let l = List.fold_left (fun acc l -> if abs l > abs acc then l else acc) 0 literals in
                let branche = solveur_dpll_rec (simplifie l clauses) (l::interpretation) in
                match branche with
                | None -> solveur_dpll_rec (simplifie (-l) clauses) ((-l)::interpretation)
                | _    -> branche
  (* Explication 
La fonction solveur_dpll_rec cherche une solution pour rendre toutes les clauses vraies. 
Si toutes les clauses sont déjà vraies, elle renvoie la solution. 
Si une clause est fausse, il n'y a pas de solution. 
Elle simplifie d'abord le problème en utilisant des clauses à un seul littéral. 
Si cela ne suffit pas, elle utilise des littéraux qui apparaissent toujours avec le même signe. 
Si elle ne trouve ni l'un ni l'autre, elle teste un littéral au hasard et continue la recherche. *)
  


(* tests *)
(* ----------------------------------------------------------- *)
(* let () = print_modele (solveur_dpll_rec systeme []) 
let () = print_modele (solveur_dpll_rec coloriage []) *)

let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses [])

    (*    NOTICE : 
      Comment compiler et exécuter le programme :
        on va dans le dossier 69 
        1. make clean ( afin de s'assurer que tout est propre)
        2. make (on compile)
        3. ./test_dpll.sh 

        le bash sert a tester tous les 2 dossiers, 
        fichier par fichier, 
        il ne fait pas tous les fichiers en meme temps
        il renvoie le nombre de SAT et UNSAT reussi
        donc A/18 et B/9
        Il fait automatiquement aussi make et make clean( mais au cas où ,
        les faire à la main.)

        Le fichier bf1355-075.cnf est ignoré
        car il est trop long à executer.


      Number of SAT results obtained: 18/18
      Number of UNSAT results obtained: 8/9 ( skipped bf1355-075.cnf)
     *)