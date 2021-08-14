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

pureCrossingCheck[block_,triplelegs_,partition_] :=
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
			       ToString[mincheck[[2]]] == ToString[maxtriple[[2]]]
		       )
		       ||
		       (
			       TrueQ[mincheck[[1]] < mintriple[[1]]]
			       &&
			       ToString[mintriple[[2]]] == ToString[maxcheck[[2]]]
		       )
		] &,
		Pick[partition, triplelegs, True]
	];


(* this is the procedure to ask if a given partition is pure crossing *)
(* it returns True, if it is pure crossing and False otherwise *)
pureCroutine[partition_] :=
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
								       pureCrossingCheck[checkblock,triplelegs,sortedpar]
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

(* This is the Moment function which calculates *)
(* \sum_{\delta \in \{b,w\}^{\times n} \sum_{\pi \in Pair(\mathcal{P}_{\delta})}} \alpha_{\pi} *)
Moment[n_] :=
	Module[{decorations,tupleslist,allPP,i,countvalue = 0},
	       (* List of all possible decorations with black and white of length n *)
	       decorations = Tuples[{b, w}, n];
	       (* we generate a list of all sequences ((type_i,color_i))_i *)
	       (* where (type_i)_i = (1,...,n) and color_i \in \{b,w\} *)
	       tupleslist =
	       Map[
		       MapThread[Union[{#1}, {#2}] &,
				      {Table[i,{i,n}], #}
		       ] &,
		       decorations
	       ];
	       Do[
		       (* all pair partitions of length n for i-th decoration *)
		       allPP = part[tupleslist[[i]]];
		       countvalue = countvalue + Count[pureCroutine[#] & /@ allPP, True],
		       {i,2^n}
	       ];
               (* Count[pureNCroutine[#] & /@ Flatten[allPP, 1], True] *)
	       countvalue
	];


(* ******************************************************************************************************* *)
(* Procedure to calculate "classical moment, i.e. Gaussian((x^{(b)} + x^{(w)})^{2k})                       *)
(* ******************************************************************************************************* *)

(* define the number of k-th Hankel Matrix *)
(* you can adjust this value for yourself, but expect something like ~ 2 hours or even more *)
(* of run-time for values k > 6 *)
(* k needs to be at least 1 *)
k = 5;

(* we generate a list with k zeros. This will be our moments vector and we fill it in the following do-loop*)
mom = Table[0,{i,2*k}];

Do[
	If[EvenQ[i],
	   mom[[i]] = Moment[i],
	   mom[[i]] = 0
	]
       ,{i,2*k}
];
Print[StringForm["These are all moments from 1 to ``:", 2*k]];
Print[mom];
Hankel = HankelMatrix[Prepend[Take[mom, k], 1], Drop[mom, k - 1]];
(* Print[Hankel // MatrixForm]; *)
Print[StringForm["This is the value of determinant of the Hankel matrix for k = ``:", k]];
Print[Assuming[{Element[q, Complexes]}, Det[Hankel]] // FullSimplify];

(* ******************************************************************************************************* *)
(* end of procedure                                                                                        *)
(* ******************************************************************************************************* *)


