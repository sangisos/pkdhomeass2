(* REPRESENTATION CONVENTION: A rectangle with sides left l, top t,
                              right r and bottom b is represented by
                              Rect(l, t, r, b).
   REPRESENTATION INVARIANT:  left<right, and bottom<top. v and
   taken from Assignment2.pdf
*)
datatype rectangle = Rect of int * int * int * int

(* REPRESENTATION CONVENTION: A quadtree with a root containing the extent e and
                              two rectangle lists v and h, the top left
                              subquadtree TL, the top right subquadtree TR,
                              the bottom left subquadtree BL and the bottom
                              right subquadtree BR is represented by
                              Qt(e, v, h, TL, TR, BL, BR);
                              The empty quadtree is represented by EmptyQuadTree
   REPRESENTATION INVARIANT:  None.
   taken from Assignment2.pdf
*)
datatype quadTree = EmptyQuadTree
                  | Qt of rectangle * rectangle list * rectangle list *
                          quadTree * quadTree * quadTree * quadTree;

exception InvalidRectangle;
exception ArgumentOutOfBounds of string;
exception ArgumentException of string;

(* validRectangle(Rect(a,b,c,d,e))
   TYPE: rectangle -> bool
   PRE: true
   POST: true if a<c and d<b, else false.
   EXAMPLE: validRectangle(Rect(1,8,8,1)) = true
*)
fun validRectangle(Rect(left,top,right,bottom)) = left<right andalso bottom<top;

(* emptyQtree e
   TYPE: rectangle -> quadTree
   PRE: true
   POST: A quadTree with extent e
   EXAMPLE: emptyQtree (Rect(2,4,4,2)) =
        Qt(Rect(2,4,4,2), [], [], EmptyQuadTree, EmptyQuadTree, EmptyQuadTree,
            EmptyQuadTree)
*)
fun emptyQtree e =
    Qt(e,[],[],EmptyQuadTree,EmptyQuadTree,EmptyQuadTree,EmptyQuadTree);

(* insert (q, r)
   TYPE: quadTree * rectangle -> quadTree
   PRE: rectangle r must be inside the extent of q.
   POST: The quadTree q with the rectangle r inserted at the correct location
         within it.
   EXAMPLE: insert(Qt(Rect(0,16,16,0), [], [], EmptyQuadTree, EmptyQuadTree,
                EmptyQuadTree, EmptyQuadTree), Rect(6,7,7,6)) =
            Qt(Rect (0, 16, 16, 0), [], [], EmptyQuadTree, EmptyQuadTree,
                Qt(Rect (0, 8, 8, 0), [], [], EmptyQuadTree,
                    Qt(Rect (5, 8, 8, 5), [Rect (6, 7, 7, 6)], [],
                        EmptyQuadTree, EmptyQuadTree, EmptyQuadTree,
                        EmptyQuadTree
                    ), EmptyQuadTree, EmptyQuadTree
                ), EmptyQuadTree)
*)
(* VARIANT: min(|r-l|,|t-b|) where r,t,l,b are the sides of the extent of q*)
fun insert ( EmptyQuadTree, rectangle) =
    raise ArgumentException("insert called with empty quad tree.")
  | insert ( q as Qt(e, vertical, horizontal, TL, TR, BL, BR), rectangle) =
    let
        val Rect(left,top,right,bottom) = e
        val centery=(top+bottom) div 2
        val centerx=(left+right) div 2
        val Rect(rectLeft,rectTop,rectRight,rectBottom) = rectangle
    in
        if not (validRectangle(rectangle)) then
            raise InvalidRectangle
        else if rectLeft < left orelse rectTop > top orelse
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
        else if rectBottom <= centery andalso centery < rectTop then
            Qt(e, vertical, rectangle::horizontal, TL, TR, BL, BR)
        else if rectLeft <= centerx andalso centerx < rectRight then
            Qt(e, rectangle::vertical, horizontal, TL, TR, BL, BR)
        else if rectRight <= centerx then (
            if rectTop <= centery then
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
        else (
            if rectBottom >= centery then
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
                  )
            )
    end;

(* query' (q as Qt(e as Rect(l,t,r,b), v, h, TL, TR, BL, BR), x, y, buffer)
   TYPE: quadTree * int * int * rectangle list -> rectangle list
   PRE: x,y must be inside the extent e.
   POST: A list of all rectangles in the quadTree q that contain the point (x,y)
   EXAMPLE: query (Qt(Rect(1,50,50,1), [Rect(20,45,45,20)], [Rect(10,20,10,20)],
        EmptyQuadTree, EmptyQuadTree, EmptyQuadTree, EmptyQuadTree), 25, 40, []) =
            [Rect(20,45,45,20)]
*)
(* VARIANT: min(|r-l|,|t-b|) *)
fun query' (EmptyQuadTree, _, _, buffer) = buffer
  | query' (Qt(Rect(left,top,right,bottom), vertical, horizontal,
        TL, TR, BL, BR), x, y, buffer) =
    let
        (* pointInRect(r)
           TYPE: rectangle -> bool
           PRE: true
           POST: true if the rectangle r contains the coordinates
                x,y from the call of query.
           EXAMPLE: pointInRect (Rect(1,4,4,1)) = true (given that x=2,y=3)
    *)
        fun pointInRect (Rect(rl,rt,rr,rb)) = rl <= x andalso x < rr andalso
                                              rb <= y andalso y < rt
        val centerx = (left+right) div 2
        val centery = (bottom+top) div 2
    in
        query'( (
            if x < centerx then (
                if y < centery then
                    BL
                else if centery < y then
                    TL
                else
                    EmptyQuadTree
                )
            else if centerx < x then (
                if y < centery then
                    BR
                else if centery < y then
                    TR
                else
                    EmptyQuadTree
                )
            else
                EmptyQuadTree
            )
            ,x,y,(List.filter (pointInRect) (vertical @ horizontal)) @ buffer
        )
    end;
(* query (q, x, y)
   TYPE: quadTree * int * int -> rectangle list
   PRE: x,y must be inside the extent of q.
   POST: A list of all rectangles in the quadTree q that contain the point (x,y)
   EXAMPLE: query (Qt(Rect(1,50,50,1), [Rect(20,45,45,20)], [Rect(10,20,10,20)],
        EmptyQuadTree, EmptyQuadTree, EmptyQuadTree, EmptyQuadTree), 25, 40) =
            [Rect(20,45,45,20)]
*)
fun query (EmptyQuadTree, _, _) = []
  | query (q, x, y) = query'(q, x, y, [])
