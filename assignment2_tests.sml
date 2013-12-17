(*
Training test cases for PKD assignment 2 (Quadtrees), HT 13
Developed by Karl S.B. (karl.sundequist@it.uu.se)
Last updated 2013-12-13 by Tjark Weber

To run these training cases:
   1) launch PolyML shell [poly]
   2) load hand-in [use "quadTree.sml"]
   3) load training set [use "assignment2_tests.sml"]
*)

(* Verify the type of the functions *)
emptyQtree : rectangle -> quadTree;
insert : quadTree * rectangle -> quadTree;
query : quadTree * int * int -> rectangle list;

local
    (* createQtree e rs
       TYPE: rectangle -> rectangle list -> quadTree
       PRE: The extent e and all rectangles rs are non-degenerate, and the
            extent contains all rectangles.
       POST: A quadtree with the extent e containing all rectangles in rs.
    *)
    fun createQtree e rs =
        List.foldl (fn (r, q) => insert (q, r)) (emptyQtree e) rs;

    (* trainingCase n
       TYPE: int -> bool
       PRE: n : [0,5)
       POST: Whether training case n passed.
     *)
    fun trainingCase 0 =
        let (* Non-overlapping rectangles *)
            val q = createQtree (Rect(0, 6, 10, 0)) 
                                [ Rect(0, 2, 4, 1), Rect(7, 5, 10, 4) ]
        in
            (* Testing one point in each of the rectangles *)
            query (q, 2, 1) = [ Rect(0, 2, 4, 1) ] andalso
            query (q, 8, 4) = [ Rect(7, 5, 10, 4) ]
        end

      | trainingCase 1 =
        let (* Overlapping rectangles stored in the same node *)
            val q = createQtree (Rect(0, 6, 10, 0))
                                [ Rect(0, 3, 10, 0), Rect(0, 6, 3, 0) ]

            (* Testing point in both of the rectangles *)
            val rs = query (q, 1, 1)
        in
            rs = [ Rect(0, 3, 10, 0), Rect(0, 6, 3, 0) ] orelse
            rs = [ Rect(0, 6, 3, 0), Rect(0, 3, 10, 0) ]
        end

      | trainingCase 2 =
        let (* Overlapping rectangles stored in different nodes *)
            val q = createQtree (Rect(0, 10, 10, 0))
                                [ Rect(4, 10, 10, 6), Rect(8, 10, 10, 8) ]

            (* Testing point in both of the rectangles *)
            val rs = query (q, 9, 9)
        in
            rs = [ Rect(4, 10, 10, 6), Rect(8, 10, 10, 8) ] orelse
            rs = [ Rect(8, 10, 10, 8), Rect(4, 10, 10, 6) ]
        end

      | trainingCase 3 =
        let (* Non-overlapping rectangles *)
            val q = createQtree (Rect(0, 6, 6, 0))
                                [ Rect(0, 2, 2, 0), Rect(4, 6, 6, 5) ]
        in
            (* Testing point in neither of the rectangles *)
            query (q, 3, 4) = []
        end

      | trainingCase 4 =
        let (* Test each quadrant respectively *)
            val qBL = createQtree (Rect(0, 5, 5, 0)) [ Rect(0, 2, 2, 0) ]
            val qBR = createQtree (Rect(0, 5, 5, 0)) [ Rect(3, 2, 5, 0) ]
            val qTL = createQtree (Rect(0, 5, 5, 0)) [ Rect(0, 5, 2, 3) ]
            val qTR = createQtree (Rect(0, 5, 5, 0)) [ Rect(3, 5, 5, 3) ]

            (* getQuads T
               TYPE: quadTree -> quadTree * quadTree * quadTree * quadTree
               PRE: true
               POST: All quadrant of T, in the order that they appear in the datatype,
                     of if T is empty then four empty quadrants.
            *)
            fun getQuads (EmptyQuadTree) =
                (EmptyQuadTree, EmptyQuadTree, EmptyQuadTree, EmptyQuadTree)
              | getQuads (Qt(_, _, _, a, b, c, d)) =
                (a, b, c, d)
        in
            (* Make sure they work before we dig into them! *)
            query(qBL, 1, 1) = [ Rect(0, 2, 2, 0) ] andalso
            query(qBR, 4, 1) = [ Rect(3, 2, 5, 0) ] andalso
            query(qTL, 1, 4) = [ Rect(0, 5, 2, 3) ] andalso
            query(qTR, 4, 4) = [ Rect(3, 5, 5, 3) ] andalso

            (* Whether everything except topLeft quadrant of qTL is empty *)
            let
                val (q1, q2, q3, q4) = getQuads(qTL)
            in
                q1 <> EmptyQuadTree andalso q2 = q3 andalso q3 = q4 andalso
                q4 = EmptyQuadTree
            end andalso

            (* Whether everything except topRight quadrant of qTR is empty *)
            let
                val (q1, q2, q3, q4) = getQuads(qTR)
            in
                q2 <> EmptyQuadTree andalso q1 = q3 andalso q3 = q4 andalso
                q4 = EmptyQuadTree
            end andalso

            (* Whether everything except bottomLeft quadrant of qBL is empty *)
            let
                val (q1, q2, q3, q4) = getQuads(qBL)
            in
                q3 <> EmptyQuadTree andalso q1 = q2 andalso q2 = q4 andalso
                q4 = EmptyQuadTree
            end andalso

            (* Whether everything except bottomRight quadrant of qBR is empty *)
            let
                val (q1, q2, q3, q4) = getQuads(qBR)
            in
                q4 <> EmptyQuadTree andalso q1 = q2 andalso q2 = q3 andalso
                q3 = EmptyQuadTree
            end
        end

      | trainingCase _ =
        false;
in
    (* runTrainingCase n
       TYPE: int -> int*bool
       PRE: n : [0,5)
       POST: (n, r), where r is whether training test n passed.
    *)
    fun runTrainingCase n =
        (n, trainingCase n);
end;

runTrainingCase 0;
runTrainingCase 1;
runTrainingCase 2;
runTrainingCase 3;
runTrainingCase 4;
