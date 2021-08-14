(* We need to load this package for the cartesian product *)
<< Combinatorica`

(* This is how we generate all pair partitions *)
(* It is taken from *)
(* https://mathematica.stackexchange.com/questions/88085/find-all-the-possible-ways-of-partitioning-a-list-into-a-set-of-pairs-of-element *)
idx[{a_, b_}] := {{a, b}}

idx[list_List] := 
	Flatten[
		Function[{row},
			 Join[First@row, #] & /@ Last@row] /@
			(({#, idx[Complement[list, #]]} &) /@ (list[[{1, #}]] & /@ 
										Range[2, Length@list])),
		1
	];

idx[n_?EvenQ] := idx[Range@n];

part[list_List /; EvenQ[Length@list]] := 
	Fold[Partition, 
	     list[[Flatten[idx[Length@list]]]],
	     {2, Length@list/2}
	];


(* This generates all triples of legs {i,j,k}, such that i,k are in one block *)
(* and j is a leg of another block *)
(* input: leg is natrual number and stands for the position of the leg in the  *)
(* partition, where partition is a list of "blocks"  {l,eps_l} *)
(* output: each block is aksed if he contributes to the setting i < j < k *)
(* the block returns True if this is the case, otherwise False *)
(* Thus we obtain a list consisting of True and False with as many entries *)
(* as the partition has blocks *)

TripleLegs[leg_,partition_] :=
	Map[
		(TrueQ[#[[1, 1]] < leg < #[[2, 1]]]) &,
		partition
	];
		


(* this is how we check if the triplelegs-tuples does not violate *)
(* the pure noncrossing condition and all inner blocks carry only one color*)
pureNCCheck[block_,triplelegs_,partition_] :=
	Map[(* we receive True if we obtain a proper nesting and the inner block is built only from *)
	    (* one color, otherwise in case there is a crossing or the inner block has mixed colors, we receive False *)
		(
			(
				IntervalMemberQ[
					Interval[{#[[1, 1]] , #[[2, 1]]}], 
					Interval[{block[[1, 1]], block[[2, 1]]}]
				]
			)
			&&
			(
				(       (* only white legs *)
					Union[{block[[1, 2]], block[[2, 2]]}] == {w}
				)
                                ||
				(       (* only black legs *)
					Union[{block[[1, 2]], block[[2, 2]]}] == {b}
				)
			)
		)&,
	         (* we only check those blocks, which satisfy the condition i < j < k *)	       
	        Pick[partition, triplelegs, True]
	];

mixedCrossingCheck[block_,triplelegs_,partition_] :=
	Map[
		Module[{mincheck,maxcheck,mintriple,maxtriple},
		       (* have better variable names *)
		       mincheck = block[[1]];
		       maxcheck = block[[2]];
		       mintriple = #[[1]];
		       maxtriple = #[[2]];
		       (* this is how we implement pure crossings check *)
		       (
			       TrueQ[maxtriple[[1]] < maxcheck[[1]]]
			       &&
			       Not[ToString[mincheck[[2]]] == ToString[maxtriple[[2]]]]
		       )
		       ||
		       (
			       TrueQ[mincheck[[1]] < mintriple[[1]]]
			       &&
			       Not[ToString[mintriple[[2]]] == ToString[maxcheck[[2]]]]
		       )
		] &,
		Pick[partition, triplelegs, True]
	];


(* this is the procedure to ask if a given partition is pure crossing *)
(* it returns True, if it is pure crossing and False otherwise *)
biNCroutine[partition_] :=
	Module[{i,j,checkblock,checkleg,triplelegs,checkvalue,sortedpar},
	       sortedpar = SortBy[#, First] & /@ partition;
	       Do[(* we enter the outer do-loop and grab the i-th block of partition *)
		       checkblock = sortedpar[[i]];
		       Do[(* we perform checks on both legs of a block *) 
			       checkleg = checkblock[[j]];
			       (* we determine, which blocks satisfy the condition i < j < k *)
			       triplelegs = TripleLegs[checkleg[[1]],sortedpar];
			       If[  
				       Union[triplelegs] == {False},
				       (* if the triplelegs-list is empty, there is nothing to check, *)
				       (* then exit the inner do-loop *)
				       checkvalue = True,
				       (* otherwise we need to perform checks on tripleleg-scenario *)
				       If[     (* if triplelegs is True for some block, then we need to perform a check *)
					       (* the triple legs scenario needs to pass the pureNCCheck OR *)
					       (* the pureCrossingCheck. We do this for each triple legs scneario, therefore *)
					       (* we have used the MapThread-construct. If each triple legs scenario passed with *)
					       (* True, we can keep the checkvalue to True and iterate in the inner loop to *)
					       (* otherwise a triple leg scenario did not pass the checks, then we set *)
					       (* the checkvalue to False and abbort the inner loop *)
					       Union[
						       MapThread[
							       Or,
							       {
								       pureNCCheck[checkblock,triplelegs,sortedpar],
								       mixedCrossingCheck[checkblock,triplelegs,sortedpar]
							       }
						       ]
					       ] == {True}
					     ,
					       checkvalue = True,
					       checkvalue = False;
					       Break[]					       
				       ]
			       ],
			       {j,1,2}
		       ];
		       (* before we continue with the outer-loop, we ask if the inner-loop has changed *)
		       (* checkvalue to False, if this is the case we abbort the outer-loop *) 
		       If[
			       checkvalue == False,
			       checkvalue = False;
			       Break[],
			       checkvalue = True
		       ]
		     ,
		     {i,1,Length[sortedpar]}
	       ];
	       checkvalue
	];



GetType[block_] := Map[First[#] &, block];
GetColor[block_] := Map[Last[#] &, block];

(* we ask if cblock and dblock have a crossing. Returns True if this is the case *)
CrossingBlocksQ[cblock_,dblock_] :=
	Module[{sortcblock,sortdblock},
	       (* ensure that our blocks are sorted *)
	       sortcblock = Sort[GetType[cblock],Less];
	       sortdblock = Sort[GetType[dblock],Less];
	       (* either the first or the last leg of dblock has position between the legs of cblock *)
	       (* this will lead to a crossing between both blocks *)
	       (IntervalMemberQ[Interval[sortcblock], First[sortdblock]]
	       &&
	       Not[IntervalMemberQ[Interval[sortcblock], Last[sortdblock]]])
	       ||
	       (IntervalMemberQ[Interval[sortcblock], Last[sortdblock]]
	       &&
	       Not[IntervalMemberQ[Interval[sortcblock], First[sortdblock]]])
	];

CombineBlocks[cblock_,dblock_] :=
	Module[{mincblock,mindblock},
	       mincblock = Min[GetType[cblock]];
	       mindblock = Min[GetType[dblock]];
	       If[TrueQ[mincblock < mindblock],
		  Prepend[{SortBy[dblock,First]},SortBy[cblock,First]],
		  Append[{SortBy[dblock,First]},SortBy[cblock,First]]
	       ]
	];
	
(* we create a list, where each entry contains 2 blocks, one is the given block, which share a crossing in the *)
(* given partition *)
CrossingBlocks[block_,part_] := 
	Module[{cblist},
	       cblist = Map[CrossingBlocksQ[block,#]&,part];
	       (* CrossingBlocksQ flags True for the block with itself, therefore we need to remove it from crossings list *)
	       cblist = Complement[Pick[part,cblist,True],{block}];
	       (* now we sort each entry *)
	       If[Length[cblist] == 0,
		  (* we return an empty list, if there are no crossings for the given block in the partition *)
		  {},
		  cblist = Map[SortBy[#,First]&,cblist];
		  (* now create pairs of crossing blocks *)
		  Map[CombineBlocks[block,#]&,cblist]
	       ]
	];

(* gives a list of all possible crossing blocks in a pair partition *)
ListofCrossings[part_] := DeleteDuplicates[Flatten[Map[CrossingBlocks[#, part] &, part], 1]];

ValueofCrossing[cross_] := Module[{color},
				  (* we already know that each crossing leads to an mixed crossing, *)
				  (* moreover the crossing already comes sorted *)
				  (* therefore we only need to look at the color of the first leg in the second block *)
				  (* get the colors of the two legs in the second block *)
				  color = GetColor[cross[[2]]];
				  (* check the color of the first leg of the second block *)
				  If[TrueQ[ToString[color[[1]]] == "w"],
                                     q,
				     Conjugate[q]
				  ]
			   ];

PolyValue[part_] := Apply[Times, Map[ValueofCrossing[#] &, ListofCrossings[part]]];


Involution[decoration_] := Reverse[decoration];
(* special treatment for units *)
Involution[{1}] := {1};

Gaussian[dec_] :=
	Module[{deco,allPP,epstuple,n},
	       (* we need to care for units *)
	       deco = DeleteCases[dec, 1];
	       (* after we have deleted all units and the list is empty, then we know *)
	       (* that we need to evaluate Gaussian[1] which is 1, since it is a state *)
	       If[Length[deco] == 0,
		  (* we return 1 in this case *)
		  1,
		  n = Length[deco];
		  If[EvenQ[n],
		     epstuple =
		     MapThread[Union[{#1}, {#2}] &, {Table[i, {i, n}], deco}];
		     (* create all pairpartitions for given eps-tuple *)
		     allPP = part[epstuple];
		     (* throw away all pair partitions, which are crossing *)
		     allPP = Pick[allPP,Map[biNCroutine[#] &,allPP], True];
		     Total[Map[PolyValue[#]&,allPP]]
		   ,
		     0
		  ]
	       ]
	];



(* ******************************************************************************************************* *)
(* Procedure to calculate delta-moment for given decoration tuple, i.e. Gaussian(x^{\delta})               *)
(* ******************************************************************************************************* *)

n = 3;
stage1 = Join[{{}, {1}}, Flatten[Map[Tuples[{b, w}, #] &, Table[i, {i, n}]], 1]];
(* we go by brute force and use the cartesian Product *)
permlist = Drop[Map[FlattenAt[#, 1] &, CartesianProduct[CartesianProduct[stage1, stage1], stage1]],1];
(* we say that the {{1},{b,w},{w,w,b}} is the same as {{1},{w,w,b},{b,w}), i.e. we order tuples by length of their entries *)
permlist = DeleteDuplicates[Map[Sort[#, Length[#1] < Length[#2] &] &, permlist]];

i = 1;
(* create an empty list *)
DetList = {};
Print["Check procedure in process ... please wait"]

While[True,
      (* remove empty entries *)
      decocopy = Pick[permlist[[i]], Map[TrueQ[Length[#] > 0] &, permlist[[i]]], True];
      column = Map[Involution[#] &, decocopy];
      gauss = Map[Gaussian[#]&, Outer[Join,column,decocopy, 1], {2}];
      DetList = AppendTo[DetList,Det[gauss]];
      If[i == Length[permlist],
	 Print["We have reached the end of the iteration"];
	 Break[]
      ];
      i++
];

Print["What are the possible cases for q, such that all determinants are greater or equal to 0 under the restriction 0 < Abs[q] <= 1?"]
Print[Reduce[Apply[And, Map[# >= 0 &, DetList]] && Abs[q] > 0 && Abs[q] <= 1, q, Complexes]];

(* ******************************************************************************************************* *)
(* end of procedure                                                                                        *)
(* ******************************************************************************************************* *)


