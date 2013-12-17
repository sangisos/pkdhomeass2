(*
DATATYPE REPRESENTATION:
INVARIANT REPRESENTATION:


*)
datatype rectangle = Rect of int * int * int * int

(*
DATATYPE REPRESENTATION:
INVARIANT REPRESENTATION:


*)
datatype quadTree = EmptyQuadTree |
	            Qt of rectangle * rectangle list * rectangle list *
			  quadTree * quadTree * quadTree * quadTree

(*
emptyQtree e
TYPE: rectangle -> quadTree
PRE: true
POST:
EXAMPLE:
    
*)
fun emptyQtree e = Qt(e,[],[],EmptyQuadTree,EmptyQuadTree,EmptyQuadTree,EmptyQuadTree);

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

