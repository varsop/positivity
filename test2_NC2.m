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
(* the non-crossing condition *)
NCCheck[block_,triplelegs_,partition_] :=
	Map[(* we receive True if we obtain a proper nesting, otherwise *)
	    (* in case there is a crossing, we receive False *)
		IntervalMemberQ[
			Interval[{#[[1, 1]] , #[[2, 1]]}], 
			Interval[{block[[1, 1]], block[[2, 1]]}]
		]&,
	        (* we only check those blocks, which satisfy the condition i < j < k *)	       
	        Pick[partition, triplelegs, True]
	];



(* this is the procedure to ask if a given partition is noncrossing *)
(* it returns True, if it is non-crossing  *)
NCroutine[partition_] :=
	Module[{i,j,checkblock,checkleg,triplelegs,checkvalue,sortedpar},
	       (* we first sort our blocks of the partitions, so that we can assure that each time we call a block *)
	       (* of the partition, that it comes already sorted *)
	       sortedpar = SortBy[#, First] & /@ partition;
	       Do[(* we enter the outer do-loop and grab the i-th block of partition and sort the two elements of the block*)
		       checkblock = sortedpar[[i]];
		       Do[(* we perform checks on both legs of a block *) 
			       checkleg = checkblock[[j]];
			       (* we determine, which blocks satisfy the condition i < j < k *)
			       triplelegs = TripleLegs[checkleg[[1]],sortedpar];
			       If[  
				       Union[triplelegs] == {False},
				       (* if the triplelegs-list only contains False, there is nothing to check, *)
				       (* then exit the inner do-loop *)
				       checkvalue = True,
				       If[(* If NCCheck spotted a crossing it returns False *)
					  (* we check if all triple legs sceanrios have passed NCCheck with True *)    
					       Union[NCCheck[checkblock,triplelegs,sortedpar]] == {True},
					       checkvalue = True,
					       (* in this case at least one triple leg scenario did not pass the pureNCCheck *)
					       checkvalue = False;
					       Break[]
				       ]
			       ],
			       {j,2}
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
		     {i,Length[sortedpar]}
	       ];
	       checkvalue
	];


GetType[block_] := Map[First[#] &, block];
GetColor[block_] := Map[Last[#] &, block];

(* gives a list of True and False, where each block of a partiton is tested to be an interval block *)
(* gives True if the block belongs could belong to an interval partition, False otherwise *)
IntervalBlockCheck[part_] :=
	Module[{type,diff},
	       (* we obtain the same partition, but with the color labels dropped *)
	       type = Map[GetType[#] &, part];
	       (* measure distance between legs of each block *)
	       diff = Map[Abs[Apply[Subtract, #]] &, type];
	       (* check if each distance is 1 *)
	       Map[TrueQ[# == 1] &, diff]
	];

InterPartCheck[part_] := TrueQ[Union[IntervalBlockCheck[part]] == {True}];


(* returns True if there is no higher block for a non-interval block *)
(* block needs to come with color labels dropped *)
NoHigherBlockCheck[block_,part_] :=
	Module[{typeblock,type},
	       typeblock = GetType[block];
	       type = Map[GetType[#] &, part];
	       (* there appears at least one True value, because the block we check contains itself *)
	       TrueQ[Count[Map[IntervalMemberQ[Interval[#], Interval[typeblock]] &, type], True] == 1]
	];

(* we want to determine all the inner blocks with respect to a given outer block *)
(* we will receive a list of all inner blocks and their color labels *)
(* we will store them in a list *)
InnerBlocks[outer_,part_] :=
	Module[{type},
	       outertype = GetType[outer];
	       type = Map[GetType[#] &, part];
	       Complement[Pick[part, Map[IntervalMemberQ[Interval[outertype], Interval[#]] &, type], True], {outer}]
	];

(* we look at the colors of the legs of the block and determine the value *)
ValueInnerBlock[block_] :=
	Module[{colors},
	       colors = GetColor[block];
	       If[TrueQ[Length[Union[colors]] == 1],
		  1,
		  If[TrueQ[ToString[colors[[1]]] == "w"],
		     q,
		     Conjugate[q]
		  ]
	       ]
	];

(* apply this to each outer block *)
(* we return a polynomial in 1,q,q^* *)
CountRoutine[outer_,part_] :=
	Module[{iblocks},
	       (* we generate a list of inner blocks for the given outer block *)
	       iblocks = InnerBlocks[outer,part];
	       (* for each entry in iblocks, we determine its value *)
	       Apply[Times,Map[ValueInnerBlock[#]&,iblocks]]
	];

(* we assume that the partition has at least one nesting *)
PolyValue[part_] :=
	Module[{outercandidates,outerblocks, outerblocksvalue},
	       (* we first need to find all the noninterval blocks in the given partition *)
	       (* we use IntervalBlockCheckto decide if a block is an interval block *)
	       outercandidates = Pick[part,IntervalBlockCheck[part],False];
	       (* for each noninterval block, we need to decide if it is an outer block *)
	       (* we receive a list of all outer blocks, which is non empty, because we have assumed *)
	       (* that it has at least one nesting *)
	       outerblocks = Pick[outercandidates,Map[NoHigherBlockCheck[#,part]&,outercandidates],True];
	       (* for each outer block we will determine its value *)
	       (* we obtain a list of polynomials in q,q^* *)
	       outerblocksvalue = Map[CountRoutine[#,part]&,outerblocks];
	       (* we return the final value as the product polynomial values of each outer block *)
	       Apply[Times,outerblocksvalue]
	];
	
	
Involution[decoration_] := Reverse[decoration];
(* special treatment for units *)
Involution[{1}] := {1};

(* calculates Gaussian(x^\delta) for \delta = (\delta_i)_i and each \delta_i is a word in \{b,w\} *)
Gaussian[dec_] :=
	Module[{deco,nNC,allPPNC,ninter,allPPinter,allPP,epstuple,n},
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
		     allPP = Pick[allPP,Map[NCroutine[#] &,allPP], True];
		     (* first we want to pick out only interval partitions *)
		     allPPinter = Pick[allPP,Map[InterPartCheck[#]&,allPP],True];
		     (* their polynomial value is 1, therefore we just need to count the entries in allPPinter *)
		     ninter = Length[allPPinter];
		     (* the remaining partitions from allPP are NC but noninterval partitions, they have *)
		     (* at least one nesting *)
		     allPPNC = Complement[allPP, allPPinter];
		     (* we determine the polynomial value for each NC partition and then sum these all up to one value *)
		     nNC = Total[Map[PolyValue[#]&,allPPNC]];
		     (* the final value of Gaussian(x^\delta), where \delta is the decoration is *)
		     ninter + nNC
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


