(* We need to load an add-on package *)
<< Combinatorica`

(* This is one approach to find all pair partitions *)
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
(* output: each block is aksed if he contributes to the setting i < j < k AND *)
(* if the color of j is white *)
(* the block returns True if this is the case, otherwise False *)
(* Thus we obtain a list consisting of True and False with as many entries *)
(* as the partition has blocks *)

TripleLegs[leg_,partition_] :=
	Map[
		((TrueQ[#[[1, 1]] < leg[[1]] < #[[2, 1]]])
		 &&
		 (ToString[leg[[2]]] == ToString[w])
		) &,
		partition
	];
		

NCAllCheck[block_,triplelegs_,partition_] :=
	Map[    (* whenever the triple legs scneario is true, i.e. i < j < k, then *)
		(* since we look at pair partitions, where each block only has two legs *)
		(* the leg j can not have the color white for interval-crossing partition *)
		(* otherwise it would belong to the same block of the legs i and k and this would constitute *)
		(* a block with at least 3 legs. Therefore the color of j needs to black *)
		(* this is the only property we need to check for interval-crossing pair partitions if we apply it to *)
		(* to the triple leg scenario *)
		(
			(
				IntervalMemberQ[
					Interval[{#[[1, 1]] , #[[2, 1]]}], 
					Interval[{block[[1, 1]], block[[2, 1]]}]
				]
			)
			&&
			(
				(* only white legs *)
				Union[{block[[1, 2]], block[[2, 2]]}] == {w}

                        )
		) &,
	         (* we only check those blocks, which satisfy the condition i < j < k *)	       
	        Pick[partition, triplelegs, True]
	];


(* this is the procedure to ask if a given partition is noncrossing-all *)
(* it returns True, if it is noncrossing-all and False otherwise *)
NCAllroutine[partition_] :=
	Module[{i,j,checkblock,checkleg,triplelegs,checkvalue,sortedpar},
	       (* first sort the blocks of the given partition *)
	       sortedpar = SortBy[#, First] & /@ partition;
	       Do[(* we enter the outer do-loop and grab the i-th block of partition *)
		       checkblock = sortedpar[[i]];
		       Do[(* we perform checks on both legs of a block *) 
			       checkleg = checkblock[[j]];
			       (* we determine, which blocks satisfy the condition i < j < k *)
			       triplelegs = TripleLegs[checkleg,sortedpar];
			       If[  
				       Union[triplelegs] == {False},
				       (* if the triplelegs-list is empty, there is nothing to check, *)
				       (* then exit the inner do-loop *)
				       checkvalue = True,
				       (* otherwise we need to perform checks on tripleleg-scenario *)
				       If[(* If pureNCCheck spotted a crossing or mixed inner blocks, *)
					  (*it returns False *)
					  (* we check if False is contained, and exit the inner-loop *)
					       Union[NCAllCheck[checkblock,triplelegs,sortedpar]]
					       == {True} ,
					       checkvalue = True,
					       checkvalue = False; Break[] ] ],
					       {j,1,2} ];
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
		     allPP = part[epstuple];
		     Count[NCAllroutine[#] & /@ allPP, True]
		   ,
		     (* Count[pureNCroutine[#] & /@ Flatten[allPP, 1], True] *)
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
Print["Check procedure in process ... please wait"]

While[True,
      (* remove empty entries *)
      (* remove empty entries *)
      decocopy = Pick[permlist[[i]], Map[TrueQ[Length[#] > 0] &, permlist[[i]]], True];
      column = Map[Involution[#] &, decocopy];
      gauss = Map[Gaussian[#]&, Outer[Join,column,decocopy, 1], {2}];
      If[
	      MemberQ[Map[TrueQ[# >= 0] &, Eigenvalues[gauss]],False],
	      Print[StringForm["This is the matrix for decorations tuple ``:", permlist[[i]]]];
	      Print[MatrixForm[Outer[Join, column, permlist[[i]], 1],TableDepth -> 2]];
	      Break[]
      ];
      If[i == Length[permlist],
	 Print["We have reached the end of the iteration and no violation of positive semi-definiteness occured."];
	 Break[]
      ];
      i++
];

(* ******************************************************************************************************* *)
(* end of procedure                                                                                        *)
(* ******************************************************************************************************* *)


