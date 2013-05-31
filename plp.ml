open Tk ;;
open Sys;;
open String;;
open Graphics;;


(*compilation
	ocamlc -I +labltk labltk.cmagraphics.cma  plp.ml -o plp 
	or
	ocamlc -I +labltk labltk.cma graphics.cma  plp.ml -o plp
*)


(***************** parser of formulas ************************)
let concat_pr w a=w^Char.escaped a;;
let concat_lw a w=(Char.escaped a)^w;;

(* counts the number of occurence of a letter 'a' in th word "s" up to i-th position*)
let rec numberOfOccurence s a i=
  if i=0 then (if s.[0]=a then 1 else 0)
  else 
    (if String.sub s 0 i=(String.sub s 0 (i-1))^(Char.escaped a) then 1+numberOfOccurence s a (i-1)
     else numberOfOccurence s a (i-1));;


let rec parenth s i= (* counts the polarisation of parentheses in the expression at the place i *)
  if i=0 then (if s.[0]='(' then (-1) else raise(Invalid_argument "Invalid expression"))
   else
    match s.[i] with
        '('->(parenth s (i-1))-1
      | ')'->(parenth s (i-1))+1
      | _->parenth s (i-1);;



let rec parenth_ll s i= (* counts the polarisation of parentheses in the expression at the place i to the left*)
  let dl=((String.length s)-1) in
  if i=0 then (if s.[dl]=')' then 1 else raise(Invalid_argument "Another invalid expression"))
   else

    match s.[(String.length s)-i-1] with
        '('->(parenth_ll s (i-1))-1
      | ')'->(parenth_ll s (i-1))+1
      | _->parenth_ll s (i-1);;







(* counts the polorisation in s at the place i_0+j starting from i_0*)
(* WARNING s.[i_0]+1 must be ')' . Otherwise exception will be raised  *)


let parenth0 s i_0 j=
  let s0=String.sub s (i_0+1) j in
    parenth s0 (j-1);;

(* counts the polorisation in s at the place i_0-j+1 starting from i_0*)
(* WARNING s.[i_0]-1 must be ')' . Otherwise exception will be raised *)

let parenth0_l s i_0 j=
  let s0=String.sub s (i_0-j-1) (j+1)
  in (parenth_ll s0 j);;



(*

let parenth0_l s i_0 j=
  let s0=String.sub s j ((String.length s)-i_0) in
  parenth_l s0 (j-1);;*)
  
let rec mainConn s i= if parenth s i=(-1) then i else (mainConn s (i+1));; 
                                                        (* finds the first place from i where polarisation  =-1 *)



type conn_11=
    Negg
| L;;

type conn_12=
    Konn
| Altt
| Impll;;

type connective= Negg
| L
| Konn
| Altt
| Impll;;

(*type connective=conn_11 of conn_11;;*)


type subdecomp=
    Complex_1 of connective*subdecomp
  | Complex_2 of connective*(subdecomp*subdecomp)
  | Atom of string;;





let string_to_connective (w: string)=match w with
    "~"->(Negg: connective)
  |"@"->L
  | "&"->(Konn: connective)
  | "v"->(Altt: connective)
  | ">"->(Impll: connective)
  | _->raise(Invalid_argument "It is not a connective");;


let rec rozp w=match Char.escaped(w.[(mainConn w 1)+1]),Char.escaped w.[1] with
    
    _,"~"|_,"@"->w.[1]
    |"&",_|"v",_|">",_->w.[(mainConn w 1)+1]
    |_->raise(Invalid_argument "There is no connective");;


let rec form_of_string w =match String.length w with
    3->Atom(Char.escaped (get w 1))
  | _->(match Char.escaped(rozp w) with
            "~"->Complex_1((Negg:connective),form_of_string (String.sub w 2 ((String.length w)-3)))
          | "@"->Complex_1((L:connective),form_of_string (String.sub w 2 ((String.length w)-3)))
          | "&"->Complex_2((Konn:connective),(form_of_string(String.sub w 1 ((mainConn w 1))),
                       form_of_string(String.sub w ((mainConn w 1)+2) (((String.length w)-(mainConn w 1))-3))))
          
					| "v"->Complex_2((Altt:connective),(form_of_string(String.sub w 1 ((mainConn w 1))),
                       form_of_string(String.sub w ((mainConn w 1)+2) (((String.length w)-(mainConn w 1))-3))))
					
					| ">"->Complex_2((Impll:connective),(form_of_string(String.sub w 1 ((mainConn w 1))),
                       form_of_string(String.sub w ((mainConn w 1)+2) (((String.length w)-(mainConn w 1))-3))))
										
					| _->Atom("a") );;





(* inserts s in string w at the place i *)
let ins w s i=try
  (String.sub w 0 i)^s^(String.sub w i ((String.length w)-i))
with Invalid_argument "String.sub"->raise(Invalid_argument "X");;


let rec var_test w i= match get w ((String.length w)-i) with
  | 'a'..'u'| 'w'..'z'->true
  | _->false;;

let rec var_testneg w i= match get w ((String.length w)-i) with
  | '~' ->true
  | _->false;;

(* encloses atomic variables by parentheses*)
let rec ins_parenth2 v i= 
  try 
    if (var_test v i) then 
      
      if (v.[(length v)-i-1]='(') && (v.[(length v)-i+1]=')') then
        ins_parenth2 v (i+1)
      else
        
        let w0=ins v "(" ((length v)-i) in
        let w1=ins w0 ")" ((length v)-i+2) in
          ins_parenth2 w1 i  
    else
      ins_parenth2 v (i+1)  
  
  with Invalid_argument "index out of bounds" -> v;;

(* prececes ins_parenth2 fixing the bug *)  

let ins_parenth3 w=let v=ins_parenth2 (" "^w) 1 in
  sub v 1 ((length v)-1);;



let ins_parenth4 w=if (get w 0='(') then w else
                           let w0=ins w ")" ((length w)) in
                             ins w0 "(" 0;;

(* for j=1 a0a1...aia_{i+1}.....a_{lgt a} seeks the first on the right place m, such that *)
(* a_{i+1}.....a_m is a formula *)

let rec dok_for w i j=if ((parenth0 w i j)=0) then (i+j)
else
  dok_for w i (j+1);;


let rec dok_for_l w i j=if ((parenth0_l w i j)=0) then (i-j-1)
else
  dok_for_l w i (j+1);;





let rec ins_naw_neg w i_0= try 
  if ((get w i_0)='~') then
    let theEnd=dok_for w i_0 1 in
      if ((get w (theEnd+1)!=')') || (get w (i_0-1)!='(')) then
        let v0=ins w ")" (theEnd+1) in
         let v1=ins v0 "(" (i_0) in
           ins_naw_neg v1 (i_0-1)
      else ins_naw_neg w (i_0-1)
else ins_naw_neg w (i_0-1)
      
with Invalid_argument "index out of bounds"->w;;

(* encloses negation by patentheses *)

let ins_parenth5 w=let v0=(ins_naw_neg (" "^w^" ") ((length w)+1)) in
                    sub v0 1 ((length v0)-2);;




let rec ins_naw_kon w i_0 (spj:char)= try 
  if ((get w i_0)=spj) then
    let theEnd=dok_for w i_0 1 in
		let pocz=dok_for_l w i_0 1 in
      if ((get w (theEnd+1)!=')') || (get w (pocz-1)!='(')) then
        let v0=ins w ")" (theEnd+1) in         
						if ((get v0 (pocz-1)!='(') || (get v0 (i_0-3)!=')')) then 
								let v3=ins v0 "(" pocz in			
           ins_naw_kon v3 (i_0-1) spj
					else ins_naw_kon w (i_0-1) spj
      else ins_naw_kon w (i_0-1) spj
else ins_naw_kon w (i_0-1) spj 
      
with Invalid_argument "index out of bounds"->w;;

(* encloses connective spj by parentheses in the expression w *)
let ins_parenth6 w (spj: char)=let v0=(ins_naw_kon (" "^w^" ") ((length w)+1) spj) in
                    sub v0 1 ((length v0)-2);;






let ins_parenth w=let v0=(ins_parenth3 w) in
										let v1=(ins_parenth5 v0) in
										let v2=(ins_parenth6 v1 '&') in
										let v3=(ins_parenth6 v2 'v') in
										ins_parenth6 v3 '>';;




let fos w=form_of_string(ins_parenth w);;



(* converts to string *)


  


let str_of_podr0 exp =
  let open_paren prec op_prec =
    
			if prec > op_prec then "(" else ""
				 in
  let close_paren prec op_prec =
    if prec > op_prec then ")" else "" in
  let rec print prec exp =     
    match exp with
        Atom c -> c
      | Complex_2(Altt,(f, g))->(open_paren prec 0)^
			(print 0 f)^"v"^(print 0 g)^(close_paren prec 0)
			|Complex_2(Konn,(f, g))->
            (open_paren prec 1)^(print 1 f)^"&"^(print 1 g)^(close_paren prec 1)     
      |Complex_2(Impll,(f, g))->
            "("^(print 2 f)^">"^(print 2 g)^")"
         
      | Complex_1(Negg, f) ->
        (open_paren prec 3)^"~"^(print 3 f)^(close_paren prec 3)
				|_->""
  in print 0 exp;;








(***************** parser of formulas ************************)
(***************** theEnd ************************)

            
            (************               typy dowodowe              *****************)
            
type for_et=subdecomp*bool;; (* pair of formulas, label +/- *)
            




type theTree=Node_1 of for_et*theTree*bool
              | Node_2 of for_et*theTree*theTree*bool
              | Leaf of for_et*bool
							| Closed of for_et list
							| Opn of for_et list;;  (*wierzcholek sklada sie z etyket.formuly typu for_et
                         oraz bool=true jesli wszystkie nastepniki poddzewa sa Closediete i false otherwise
												oraz bool=true jesli wczesniej z wierzcholka wnioskowano*)






let rec wid drz=let maks x y= if x<y then y else x in
	
	
	match drz with
	| Node_2(fm,d0,d1,_)->5+(maks (wid d0) (wid d1)) 
	| _->0;;




(*dodaje konsekwencje formuly alf do lisci drzewa dowodu*)


							
let rec rozwidz (w:theTree) (alf:for_et)=match w,alf with
							
							| Node_1(et,v,war),_->Node_1(et,(rozwidz v alf),war)
							
							
							| Node_2(et,v1,v2,war),alf->
                Node_2(et,(rozwidz v1 alf),(rozwidz v2 alf),war)
       	
							|Leaf(a,war),(Complex_1(Negg,fm),wm)->
								Node_1(a,Leaf((fm,(not wm)),war),false)
							
							| Leaf(a,war),(Complex_2(Altt,(fm0,fm1)),false)->
								
								let nast1=Leaf((fm1,false),false) in
								let nast0=Node_1((fm0,false),nast1,false) in 
								Node_1(a,nast0,war)
							
							| Leaf(a,war),(Complex_2(Altt,(fm0,fm1)),true)->
								
								let nast1=Leaf((fm0,true),false) in
								let nast2=Leaf((fm1,true),false) in 
				
								Node_2(a,nast1,nast2,war)
							
							| Leaf(a,war),(Complex_2(Konn,(fm0,fm1)),true)->
								
								let nast1=Leaf((fm1,true),false) in
								let nast0=Node_1((fm0,true),nast1,false) in 
								Node_1(a,nast0,war)
								
							| Leaf(a,war),(Complex_2(Konn,(fm0,fm1)),false)->
								
								let nast1=Leaf((fm0,false),false) in
								let nast2=Leaf((fm1,false),false) in 
								Node_2(a,nast1,nast2,war)
								
							| Leaf(a,war),(Complex_2(Impll,(fm0,fm1)),false)->
								
								let nast1=Leaf((fm1,false),false) in
								let nast0=Node_1((fm0,true),nast1,false) in 
								Node_1(a,nast0,war)
								
							| Leaf(a,war),(Complex_2(Impll,(fm0,fm1)),true)->
								
								let nast1=Leaf((fm0,false),false) in
								let nast2=Leaf((fm1,true),false) in 
								Node_2(a,nast1,nast2,war)
								
								|_->w;;
							
(*czesc wlasciwa dodawania konsekwencji pierwszego wierzcholka, z ktorego nie wnioskowano*)
							
let rec find (w:theTree) jest=match w,jest with
								|	Node_1(et,v,true),false->Node_1(et,(find v false),true)
								|	Node_2(et,v1,v2,true),false
																	->Node_2(et,(find v1 false),(find v2 false),true)
								|	Leaf(et,true),false->w

								|	Node_1(et,v,false),false->Node_1(et,(rozwidz v et),true)
								|	Node_2(et,v1,v2,false),false
																	->Node_2(et,(rozwidz v1 et),(rozwidz v2 et),true)
								|	Leaf(et,false),false-> rozwidz (Leaf(et,true)) et

								|_->w;;
								

						





(*wyluskuje fomule Atom*bool z wierzcholka*)

let atl_of_drz d=

let atl_of_podr (fm:for_et)=match fm with
	| Atom(p),w->[((Atom(p),w):for_et)]
	| _->[]
	
 in
							match d with
					| Node_2(fm,_,_,_)|Node_1(fm,_,_)| Leaf(fm,_)->atl_of_podr fm
					|Closed(l)| Opn(l)->l;;




let dodaj (d,l)=match d with
	| Node_2(fm,v0,v1,war)->Node_2(fm,v0,v0,war),((atl_of_drz d)@l)
	| Node_1(fm,v,war)->Node_1(fm,v,war),((atl_of_drz d)@l)
	| Leaf(fm,war)->Leaf(fm,war),((atl_of_drz d)@l)
	| Closed(l0)->Closed(l0@l),l
	| Opn(l0)->Opn(l0@l),l;;


(*rozwidza theTree o element Opn(lista), gdzie lista to atomy wstepujace w galezi, korzysta z funkcji dodaj*)

let rec sumuj (d:theTree) (l:for_et list)=match d with
	| Node_2(fm,v0,v1,war)->Node_2(fm,(sumuj v0 (l@(atl_of_drz d))),(sumuj v1 (l@(atl_of_drz d))),war)
	| Node_1(fm,v,war)->Node_1(fm,(sumuj v (l@(atl_of_drz d))),war)
	| Leaf(fm,war)->Node_1(fm,Opn((atl_of_drz d)@l),war)
	|_->d;;
	


let meta_neg ((fm,war):for_et)=(fm,(not war));;

			
(* dla m=[] sprawdza czy w liscie a::l wystepuje sprzecznosc i zwraca liste zlozona z tego*)
(* wywolujacego sprzecznosc, oraz liste atomow w przeciwnym przypadku, ostrzezenie nieistotne*)
			
let rec cons ((a:for_et)::l) m=if (List.mem (meta_neg a) l) then ([a],false)
															else match l with 
																| []->
																			(
																		if (List.mem a l) then (m,true)
																			else (a::m),(true)                      
																			)
																	
																| _->
																		(
																		if (List.mem a l) then (cons l m)
																	else
																	(cons l (a::m))
																	 		)
																							;;

	


(*
let rec ls_at (w:theTree),lista=match w with
	| Node_1(et,v,x,y)->Node_1(et,(ls_at v lista),x,y),lista
	| Node_2(et,v,v1,x,y)->Node_1(et,(ls_at v lista),(ls_at v lista),x,y),lista;;
*)


(*grafika drzewa o korzeniu w miejscu x,y*)



let rec draw1 (d:theTree) x y=let factor=15 in
match d with
	| Node_1((fm,et),d1,war)->moveto (x-10) (y-15); draw_string((str_of_podr0 fm)^" "^(string_of_bool et)); moveto x y;
	 lineto x (y+30); moveto x y; draw1 d1 x (y+60)
	|Node_2((fm,et),d1,d2,war)->moveto (x-10) (y-15); draw_string((str_of_podr0 fm)^" "^(string_of_bool et));
		moveto x y; lineto (x-30-((wid d)*factor)) (y+30); moveto x y; lineto (x+30+((wid d)*factor)) (y+30); moveto x y;
		draw1 d1 (x-20-((wid d)*factor)) (y+50); draw1 d2 (x+40+((wid d)*factor)) (y+50)
		
	| Opn(l)->moveto (x-10) (y-15);
	
	if (snd(cons l [])) then draw_string("consist") else draw_string("contr");
	
	
	  moveto x y;;

		
let oneStep d=find d false;;
	
let rec steps d i=if i=0 then d else oneStep (steps d (i-1));;













	
let letDraw(w)=
let ()=close_graph() in


let dd= (let alf=fos (w) in
		Leaf((alf,false),false)) in

let ee=sumuj (steps dd 12) [] 
in

let ()=open_graph " 1000x1000" in
draw1 ee 500 100;;





















let top = openTk () ;;
Wm.title_set top "plp" ;;
let v = Textvariable.create () ;;
Textvariable.set v "" ;;
let l = Label.create
    ~textvariable:v top ;;
let n = Entry.create ~width:50
    ~relief:`Sunken top ;;
(* Now the text displayed in label l
   is updated only when you press button b. *)
let b = Button.create
	~width:12
    ~text:"Echo"
    ~command:(fun () -> Textvariable.set v (Entry.get n))
    top ;;

let bb = Button.create
	~width:12
    ~text:"Prove"
    ~command:(fun () -> letDraw(Entry.get n))
    
    
    top ;;







let bq = Button.create
    ~width:12
    ~text:"The end"
    ~command:(fun () ->
      Printf.printf "%s\nBye.\n" (Entry.get n) ;
      closeTk () ; exit 0)
    top ;;
pack [coe l;coe n;coe b;coe bb;coe bq] ;;
let _ = Printexc.print mainLoop ();;
