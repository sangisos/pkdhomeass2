(*
DATATYPE REPRESENTATION:
INVARIANT REPRESENTATION:
taken from Assignment2.pdf 

*)
datatype rectangle = Rect of int * int * int * int

(*
DATATYPE REPRESENTATION:
INVARIANT REPRESENTATION:


*)
datatype quadTree = EmptyQuadTree |
	            Qt of rectangle * rectangle list * rectangle list *
			  quadTree * quadTree * quadTree * quadTree
exception InvalidRectangle;
exception ArgumentOutOfBounds of string;
exception ArgumentException of string;
fun validRectangle(Rect(left,top,right,bottom)) = left<right andalso bottom<top;

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
fun insert ( EmptyQuadTree, rectangle) = raise ArgumentException("insert called with empty quad tree.")
  | insert ( q as Qt(e, vertical, horizontal, TL, TR, BL, BR), rectangle) =
    let
	val Rect(left,top,right,bottom) = e
	val centery=(top+bottom) div 2
	val centerx=(left+right) div 2
	val Rect(rectLeft,rectTop,rectRight,rectBottom) = rectangle
    in
	if not (validRectangle(rectangle)) then
	    raise InvalidRectangle
	else if
	   rectLeft < left orelse rectTop >= top orelse
	   rectRight >= right orelse rectBottom < bottom then
	    raise ArgumentOutOfBounds("Rectangle not in extent")
	else if rectTop >= centery andalso rectBottom < centery then
	    Qt(e, rectangle::vertical, horizontal, TL, TR, BL, BR)
	else if rectLeft >= centerx andalso rectRight < centerx then
	    Qt(e, vertical, rectangle::horizontal, TL, TR, BL, BR)
	else
	    EmptyQuadTree
    end;

insert(Qt(Rect(1,9,5,6), [], [], EmptyQuadTree, EmptyQuadTree, EmptyQuadTree, EmptyQuadTree), Rect(3,8,4,6));

(*
query (q, x, y)
TYPE:
PRE:
POST:
EXAMPLE:


*)

