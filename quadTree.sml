(*
DATATYPE REPRESENTATION: Represents a rectangle by four coordinates. 
						 Coordinates represents in order:
						 left side's x-coordinate, top side's y coordinate,
						 right side's x-coordinate, bottom 
						 side's y-coordinate.
INVARIANT REPRESENTATION: Coordinates must be of type int. Coordinates' must 
						  have the following relation: 
						  bottom < top and left < right
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
TYPE: quadTree * rectangle -> quadTree
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
	   rectLeft < left orelse rectTop > top orelse
	   rectRight > right orelse rectBottom < bottom then
	    raise ArgumentOutOfBounds("Rectangle (" ^
				      Int.toString(rectLeft) ^ "," ^
				      Int.toString(rectTop) ^ "," ^
				      Int.toString(rectRight) ^ "," ^
				      Int.toString(rectBottom) ^
				      ") not in extent (" ^
				      Int.toString(left) ^ "," ^
				      Int.toString(top) ^ "," ^
				      Int.toString(right) ^ "," ^
				      Int.toString(bottom) ^ ")")
	else if rectTop > centery andalso rectBottom <= centery then
	    Qt(e, rectangle::vertical, horizontal, TL, TR, BL, BR)
	else if rectRight > centerx andalso rectLeft <= centerx then
	    Qt(e, vertical, rectangle::horizontal, TL, TR, BL, BR)
	else if rectRight <= centerx then
	    (if rectTop <= centery then
		Qt(e, vertical, horizontal, TL, TR, insert(
			if BL = EmptyQuadTree then
			    (emptyQtree(Rect(left,centery,centerx,bottom)))
			else
			    BL, rectangle),
		   BR)
	    else
		Qt(e, vertical, horizontal, insert( 
			if TL = EmptyQuadTree then
			    (emptyQtree(Rect(left,top,centerx,centery+1)))
			else
			    TL, rectangle),
		   TR, BL, BR))
	else
	    (if rectBottom >= centery then
		Qt(e, vertical, horizontal, TL, insert(
			if TR = EmptyQuadTree then
			    (emptyQtree(Rect(centerx+1,top,right,centery+1)))
			else
			    TR, rectangle), 
		   BL, BR)
	    else 
		Qt(e, vertical, horizontal, TL, TR, BL, insert(
			if BR = EmptyQuadTree then
			    (emptyQtree(Rect(centerx+1,centery,right,bottom)))
			else
			    BR, rectangle)
		   ))
    end;

insert(Qt(Rect(0,16,16,0), [], [], EmptyQuadTree, EmptyQuadTree,
	  EmptyQuadTree, EmptyQuadTree), Rect(6,7,7,6));

(*
query (q, x, y)
TYPE: quadTree * int * int -> rectangle list
PRE:
POST:
EXAMPLE:


*)

fun query (EmptyQuadTree, _, _) = []
  | query (Qt(Rect(left,top,right,bottom), vertical, horizontal, TL, TR, BL, BR), x, y) =
    let
	fun pointInRect (Rect(rl,rt,rr,rb)) = rl <= x andalso x < rr andalso rb <= y andalso y < rt
	val centerx = (left+right) div 2
	val centery = (bottom+top) div 2
    in
	(List.filter (pointInRect) (vertical @ horizontal)) @
	(if x < centerx then
	    (if y < centery then
		query(BL,x,y)
	    else if centery < y then
		query(TL,x,y)
	    else
		[])
	else if centerx < x then
	    (if y < centery then
		query(BR,x,y)
	    else if centery < y then
		query(TR,x,y)
	    else
		[])
	else
	    [])
    end;
