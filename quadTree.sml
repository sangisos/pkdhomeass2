
datatype rectangle = Rect of int * int * int * int

datatype quadTree = EmptyQuadTree |
	            Qt of rectangle * rectangle list * rectangle list *
			  quadTree * quadTree * quadTree * quadTree
(*
emptyQtree e
TYPE:
PRE:
POST
EXAMPLE
    
*)


(* 
insert (q, r)
TYPE:
PRE:
POST
EXAMPLE

*)


(*
query (q, x, y)
TYPE:
PRE:
POST:
EXAMPLE:


*)

