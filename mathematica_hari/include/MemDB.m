(* ::Package:: *)

BeginPackage["MemDB`"];
(* overview and shortcuts for the internal structure of the data base *)

NewMemDB::usage="NewMemDB[] creates an empty data base"
Format[db_MemDB]:=StringForm["< -MemDB- ``>",db[[1]]];

(* label a certain key as a data key. Data keys are handled differently.
Main difference: We never create a dispatch table to locate values *)

MemDBSetDataKey::usage="MemDBSetDataKey[db,datakey,autoapplyget,autoapplyset] label a certain key as a data key. Data keys are handled differently. \
Main difference: We never create a dispatch table to locate values. To retrieved data, the function autoapplyget is automatically applied. \ 
Likewise, each time a value is set/appended, autoapplyset is automatically applied to the value before the data is stored.";

MemDBGrowValueList::usage = "MemDBGrowValueList[db,spec] used mainly internally \
to add a value for a key, automatically applies the autoapply fcn. spec is of the form key->value." ;

MemDBAppend::usage="MemDBAppend[db,specs] insert an item into the data base. \
specs is of the form {key1->value1,key2->value2,...}. The command MemDBAppend[db,db2] appends the entire data base db2.
For new keys, the data key and auto-apply settings are taken over from db2." ;

Options[MemDBSelect]={Selection->All,RequireUnique->False};
MemDBSelect::usage = "MemDBSelect[db,specs] returns indices to data base entries that comply with the selections. \
specs is of the form {key1->value1,key2->value2,...}. The option Selection can be used to refine a selection, 
by specifying a list of integer indices to start with." 
MemDB::invkey="Error: Unknown key names!";

Options[MemDBSelectUnique]=Options[MemDBselect];
MemDBSelectUnique::usage = "MemDBSelectUnique[db,specs] works the same way as MemDBSelect, except that a
single integer index is returned. If no entry is found for the specified criteria, or if several entries are found,
this command returns an error."
MemDB::nfound="Error: No entry found for the specified criteria!";
MemDB::nuniq="Error: Several entries found for the specified criteria!";


MemDBGet::usage="MemDBGet[db,ind,key] 
various functions to retrieve information for a given integer index / list of integer indices / key / list of keys. \
If no key is specified, all data for a given data base entry is returned, in the form {key1->value1,...}. \
Otherwise, only the value(s) for the requested indice(s) and key(s) are returned, in the form of a single value, list or array, \
depending on the structure of the request. In this case, MemDBGet aborts if the requested keys are not present."
MemDB::noval="Error: No values for some of the requests.";

Options[MemDBSplit]={Selection->All};
MemDBSplit::usage="MemDBSplit[db,samekeys,OptionsPattern[]] \
gives a list containing lists of indices belonging to database entries with identical values for the keys specified in samekeys. \
samekeys is of the form {key1,key2,...}."

Options[MemDBZip]={Selection->All, AutoApplyFunctions->{}};
MemDBZip::usage = "MemDBZip[db,samekeys,indexvar,evalexpr,OptionsPattern[]] \
splits the database into pieces that have identical values in the keys specified in samekeys. \
MemDBZip then iterates over these pieces, each time evaluating evalexpr, \ 
where indexvar is set to the corresponding indices. The function returns the \ 
evaluated expressions as a list.
MemDBZip[db,samekeys,indexvar,datakey,evalexpr,OptionsPattern[]] behaves similarly, \ 
but the result is stored in the datakey field of a new database.
The auto-apply functions are taken over from the original data base as specified for datakey,
if not specified otherwise with the option AutoApplyFunctions->{<autoapplygetfcn>,<autoapplysetfcn>}."

MemDBCopyIndex::usage = "MemDBCopyIndex[dbfrom,dbto,copykeys] \
used mainly internally to create a new database (dbto) with a list of keys (copykeys) copied from the original database.
No keys are labelled as data keys."

Options[MemDBMap]={Selection->All, AutoApplyFunctions->{}};
MemDBMap::usage = "MemDBMap[db,datakey,fun2arg,OptionsPattern[]] \
creates a new data base, iterating over the old one and replacing the contents of datakey \
by the value obtained from the function fun2arg[]. This function is evaluated with two arguments, \
No.1 : original data value, No.2 : index of the entry in db."

MemDBSet::usage = "MemDBSet[db,index,keyname,value] 
sets the value belonging to the specified keyname for the specified index." 

MemDBSetGlobals::usage="MemDBSetGlobals[db,globals] sets the info stored in the globals area. "

MemDBGetGlobals::usage="MemDBGetGlobals[db] gets the info stored in the globals area."

Options[MemDBListValues]={Selection->All};
MemDBListValues::usage = "MemDBListValues[db,key,OptionsPattern[]] lists all different values that occur for the specified key";

Options[MemDBCalcKey]={Selection->All,AutoApplyFunctions->{Identity,Identity},DataKey->False};
MemDBCalcKey::usage="MemDBCalcKey[db,newkey,indexvar,expr_,OptionsPattern[]] \
creates a new key newkey if needed, otherwise overwrites the existing key of that name. \
The option values AutoApplyFunctions and DataKey are only taken in to account if a new key is appended. \
The default value of DataKey is False. If set to True, the new key has the properties of a data key. \
The default value for AutoApplyFunctions is {Identity,Identity}; this can be modified to \
apply functions to the data upon retrieval and insertion into the data base. \
The function MemDBCalcKey iterates over the data base entries, always evaluating expr, where \
indexvar points to the data element currently processed. The result of the evaluation is stored in the key newkey. \
Potentially, data previously stored there is overwritten."

MemDBTrimMemory::usage = "MemDBTrimMemory[db] releases superfluous memory allocations \
and prepares the data base for saving it to disk."


Begin["`Private`"];

(* overview and shortcuts for the internal structure of the data base *)
KeyNames[db_MemDB]:=db[[1]];
KeyNameDispatch[db_MemDB]:=db[[2]];
ValueListLengths[db_MemDB]:=db[[3]]
ValueLists[db_MemDB]:=db[[4]];
ValueDispatches[db_MemDB]:=db[[5]];
KeyCombinations[db_MemDB]:=db[[6]];
CombinationsLength[db_MemDB]:=db[[7]];
DataKeys[db_MemDB]:=db[[8]];
AutoApplyGet[db_MemDB]:=db[[9]]; 
AutoApplySet[db_MemDB]:=db[[10]]; 
GlobalInfo[db_MemDB]:=db[[11]];  (* not used, yet *)

NewMemDB[]:=MemDB[{},Dispatch[{}],{},{},{},{},0,{},{},{},{}];

(* used internaly to add a key;
 initialize all dataelements to have no entry for this key *)
SetAttributes[MemDBGrowKeys,HoldFirst];
MemDBGrowKeys[db_Symbol,keylist:{_Symbol...}] := 
Module[{newkeys,tmp},
	newkeys=Complement[keylist,KeyNames[db]];
	If[Length[newkeys]>0,
		db[[1]]=Join[KeyNames[db],newkeys];
		db[[2]]=Dispatch[MapIndexed[#1->#2[[1]]&,KeyNames[db]]];
		tmp=Array[0&,{Length[newkeys],Length[KeyCombinations[db]]}];
		If[Length[KeyCombinations[db]]>0,
			db[[6]]=Transpose[Join[Transpose[KeyCombinations[db]],tmp]];
		];
		db[[3]]=Join[ValueListLengths[db],Table[0,{Length[newkeys]}]];
		db[[4]]=Join[ValueLists[db],Table[{},{Length[newkeys]}]];
		db[[5]]=Join[ValueDispatches[db],Table[{},{Length[newkeys]}]];
		db[[9]]=Join[AutoApplyGet[db],Table[Identity,{Length[newkeys]}]];
		db[[10]]=Join[AutoApplySet[db],Table[Identity,{Length[newkeys]}]];
	];
];

(* label a certain key as a data key. Data keys are handled differently.
Main difference: We never create a dispatch table to locate values *)
SetAttributes[MemDBSetDataKey,HoldFirst];
MemDBSetDataKey[db_Symbol,datakey_Symbol,autoapplyget_:Identity,autoapplyset_:Identity] := 
Module[{keyindex},
	MemDBGrowKeys[db,{datakey}];
	keyindex=datakey/.KeyNameDispatch[db];
	db[[8]]=Union[DataKeys[db],{keyindex}];
	(* delete existing dispatch if present: *)
	db[[5,keyindex]]={}; 
	db[[9,keyindex]]=autoapplyget;
	db[[10,keyindex]]=autoapplyset;
];

(* used internally to locate a value of a key; don't apply autoapply fcn. to valueraw *)
SetAttributes[FindValueIndex,HoldFirst];
FindValueIndex[db_Symbol,keyindex_Integer,valueraw_] := 
Module[{disp,res,value2},
	If[db[[5,keyindex]]=={} ,
		(* make a new dispatch *)
		db[[5,keyindex]]=Dispatch[MapIndexed[#1->#2[[1]]&,db[[4,keyindex,1;;db[[3,keyindex]]]]]]; 
	];
	value2=valueraw; (* no autoapply fcn.  *)
	res=Replace[value2,db[[5,keyindex]]];
	If[!(Head[res]===Integer),Return[0]];
	If[res===value2,(*oops, we don't know what's going on*)
		If[res>=1
			&& res<=db[[3,keyindex]]
			&& db[[4,keyindex,res]]===value2,
			Return[res],Return[0]
		];
	];
	res
];

(* used internally to add a value for a key, automatically applies the autoapply fcn. *)
SetAttributes[MemDBGrowValueListI,HoldFirst];
MemDBGrowValueListI[db_Symbol,keyindex_Integer,value_] := 
Module[{key,append,valueindex,val},
	val=db[[10,keyindex]][value]; (* eval. autoapply fcn. *)
	If[!MemberQ[DataKeys[db],keyindex],
		valueindex=FindValueIndex[db,keyindex,val];
		If[valueindex>0,Return[{keyindex,valueindex}]];
		];
	If[Length[db[[4,keyindex]]]<10,
		AppendTo[db[[4,keyindex]],val];
		db[[3,keyindex]]++,
		If[Length[db[[4,keyindex]]]<=db[[3,keyindex]],
			db[[4,keyindex]]=Join[db[[4,keyindex]],db[[4,keyindex]]];
		];
		db[[4,keyindex,++db[[3,keyindex]]]]=val;
	];
	db[[5,keyindex]]={};
	{keyindex,db[[3,keyindex]]}
];

SetAttributes[MemDBGrowValueList,HoldFirst];
MemDBGrowValueList[db_Symbol,spec_Rule] := 
Module[{key,keyindex,append,valueindex,val},
	key=spec[[1]];
	keyindex=key/.KeyNameDispatch[db];
	If[!Head[keyindex]===Integer,
		Message[MemDB::invkey]; Abort[];
	];
	MemDBGrowValueListI[db,keyindex,spec[[2]]]
];

(* used to insert an item into the data base *)
SetAttributes[MemDBAppend,HoldFirst];
MemDBAppend[db_Symbol,specs:{_Rule...}] := 
Module[{spec,tmp,pos},
	MemDBGrowKeys[db,specs[[All,1]]];
	tmp=Map[Function[{spec},
		MemDBGrowValueList[db,spec]
		], specs];
	If[Length[db[[6]]]<= db[[7]],
		db[[6]]=Join[db[[6]],Array[0&,{10+Length[db[[6]]],Length[KeyNames[db]]}]];
	];
	pos=++db[[7]];
	Scan[(db[[6,pos,#[[1]]]]=#[[2]])&,tmp]
];

(* used to join data bases *)
SetAttributes[MemDBAppend,HoldFirst];
MemDBAppend[db_Symbol,indb_MemDB] := 
Module[{newkeys,newkeyInInd,newkeyOutInd,keyindconv,destkeyind,srckeyind,offs,len,newdat,convtab},
	newkeys=Complement[indb[[1]],db[[1]]];
	newkeyInInd=newkeys/.indb[[2]];
	MemDBGrowKeys[db,newkeys];
	db[[2]]=Dispatch[MapIndexed[#1->#2[[1]]&,KeyNames[db]]];
	newkeyOutInd=newkeys/.db[[2]];
	keyindconv=MapIndexed[#2[[1]]->(#1/.db[[2]])&,indb[[1]]];
	(* copy data key properties and auto apply functions for the new keys *)
	db[[8]]=Join[db[[8]],Select[indb[[8]]/.keyindconv,MemberQ[#,newkeyOutInd]&]];
	Scan[(
		db[[9,(#/.keyindconv)]]=indb[[9,#]];
		db[[10,(#/.keyindconv)]]=indb[[10,#]];
		)&,newkeyInInd];
	(* reserve space for the combinations *)
	If[Length[db[[6]]] < db[[7]] + indb[[7]],
		db[[6]]=Join[db[[6]],Array[0&,{Max[Length[db[[6]]],indb[[7]]],Length[KeyNames[db]]}]];
	];
	(* copy data, column wise *)
	Map[Function[{conv},
		srckeyind = conv[[1]];
		destkeyind = conv[[2]];
		offs=db[[3,destkeyind]];
		If[MemberQ[db[[8]],destkeyind],
			(* it's a data key *)
			(* Make space for the data*)
			len=indb[[3,srckeyind]];
			If[len>=offs,
				(* copy by joining *)
				db[[4,destkeyind]]=Join[db[[4,destkeyind,1;;offs]],indb[[4,srckeyind]]],
				(* otherwise grow exponentially, then copy *)
				While[Length[db[[4,destkeyind]]]<offs+len,
					db[[4,destkeyind]]=Join[db[[4,destkeyind]],db[[4,destkeyind]]];
				];
				(* now copy the data *)
				db[[4,destkeyind,offs+1;;offs+len]]=indb[[4,srckeyind,1;;len]];
			];
			db[[3,destkeyind]]+=len;
			(* now copy the key combinations *)
			newdat=indb[[6,1;;indb[[7]],srckeyind]];
			newdat=Map[If[#==0,0,#+offs]&,newdat];
			db[[6,db[[7]]+1;;db[[7]]+indb[[7]],destkeyind]]=newdat;
			,
			(* done. now the much harder case: it's not a data key *)
			newdat=Complement[indb[[4,srckeyind,1;;indb[[3,srckeyind]]]],db[[4,destkeyind,1;;offs]]];
			(* Make space for the data*)
			len=Length[newdat];
			If[len>=offs,
				(* copy by joining *)
				db[[4,destkeyind]]=Join[db[[4,destkeyind,1;;offs]],newdat],
				(* otherwise grow exponentially, then copy *)
				While[Length[db[[4,destkeyind]]]<offs+len,
					db[[4,destkeyind]]=Join[db[[4,destkeyind]],db[[4,destkeyind]]];
				];
				(* now copy the data *)
				db[[4,destkeyind,offs+1;;offs+len]]=newdat;
			];
			db[[3,destkeyind]]+=len;
			(* make a new dispatch *)
			db[[5,destkeyind]]=Dispatch[MapIndexed[#1->#2[[1]]&,db[[4,destkeyind,1;;db[[3,destkeyind]]]]]]; 
			(* create conversion table for the combinations *)
			convtab=MapIndexed[(#2[[1]]->Replace[#,db[[5,destkeyind]]])&,indb[[4,srckeyind,1;;indb[[3,srckeyind]]]]];
			(* now copy the key combinations *)
			newdat=indb[[6,1;;indb[[7]],srckeyind]]/.convtab;
			db[[6,db[[7]]+1;;db[[7]]+indb[[7]],destkeyind]]=newdat;				
		];
	],keyindconv];
	db[[7]]+=indb[[7]];
];

(* returns indices that comply with the selections *)
SetAttributes[MemDBSelect,HoldFirst];
MemDB::invkey="Error: Unknown key names!";
MemDBSelect[db_Symbol,specs:{(_Symbol->_)...},OptionsPattern[]] := 
Module[{keyindices,valindices,tmp,domain,subdb,pos},
	keyindices=specs[[All,1]]/.KeyNameDispatch[db];
	If[!And@@((Head[#]===Integer)&/@keyindices),
		Message[MemDB::invkey]; Abort[];
	];
	(*evaluate autoapply fcn. before calling FindValueIndex!*)
	valindices=MapThread[FindValueIndex[db,#1,db[[10,#1]][#2]]&,{keyindices,specs[[All,2]]}]; 
	If[Or@@(#===0&/@valindices),Return[{}]];
	domain=OptionValue[Selection];
	If[domain===All,
		Position[db[[6,1;;db[[7]],keyindices]],valindices,{1}][[All,1]],
		If[MatchQ[domain,{_Integer...}],
			pos = Position[db[[6,domain,keyindices]],valindices,{1}][[All,1]];
			domain[[pos]],
			subdb=MapIndexed[{#1,#2[[1]]} &, db[[6,1;;db[[7]],keyindices]]];
			subdb=subdb[[domain]];
			Select[subdb,(#[[1]] == valindices) &][[All,2]]
		]
	]
]

MemDB::nfound="Error: No entry found for the specified criteria!";
MemDB::nuniq="Error: Several entries found for the specified criteria!";
SetAttributes[MemDBSelectUnique,HoldFirst];
MemDBSelectUnique[db_Symbol,specs:{(_Symbol->_)...},opts:OptionsPattern[]] := 
Module[{res},
	res = MemDBSelect[db,specs,opts];
	If[Length[res]==0,Message[MemDB::nfound]; Abort[]];
	If[Length[res]>1,Message[MemDB::nuniq]; Abort[]];
	res[[1]]
]



SetAttributes[MemDBGet,HoldFirst];
MemDB::noval="Error: No values for some of the requests.";
MemDBGet[db_Symbol,indices:{_Integer...},keys:{_Symbol...}]:=Module[{keyindices,valind},
	If[Length[indices]===0,Return[{}]];
	keyindices=keys/.KeyNameDispatch[db];
	If[!And@@((Head[#]===Integer)&/@keyindices),
		Message[MemDB::invkey]; Abort[];
	];
	valind=Transpose[db[[6,indices,keyindices]]];
	If[MemberQ[valind,0,{2}],
		Message[MemDB::noval];
		Abort[];
	];
	(* apply autoapply function before returning the data *)
	Transpose[MapThread[Function[{vi,ki},db[[9,ki]]/@db[[4,ki,vi]]],{valind,keyindices}]]
]

MemDBGet[db_Symbol,indices:{_Integer...},key_Symbol]:=Module[{keyindex,valind},
	If[Length[indices]===0,Return[{}]];
	keyindex=key/.KeyNameDispatch[db];
	If[!Head[keyindex]===Integer,
		Message[MemDB::invkey]; Abort[];
	];
	valind=db[[6,indices,keyindex]];
	If[MemberQ[valind,0,{1}],
		Message[MemDB::noval];
		Abort[];
	];
	(* apply autoapply function before returning the data *)
	db[[9,keyindex]]/@db[[4,keyindex,valind]]
]

MemDBGet[db_Symbol,index_Integer,keys:{_Symbol...}]:=Module[{keyindices,valind},
	keyindices=keys/.KeyNameDispatch[db];
	If[!And@@((Head[#]===Integer)&/@keyindices),
		Message[MemDB::invkey]; Abort[];
	];
	valind=db[[6,index,keyindices]];
	If[MemberQ[valind,0,{2}],
		Message[MemDB::noval];
		Abort[];
	];
(* apply autoapply function before returning the data *)
	MapThread[db[[9,#1]][db[[4,#1,#2]]]&,{keyindices,valind}]
]

MemDBGet[db_Symbol,index_Integer,key_Symbol]:=Module[{keyindex,valind},
	keyindex=key/.KeyNameDispatch[db];
	If[!Head[keyindex]===Integer,
		Message[MemDB::invkey]; Abort[];
	];
	valind=db[[6,index,keyindex]];
	If[valind===0,
		Message[MemDB::noval];
		Abort[];
	];
	(* apply autoapply function before returning the data *)
	db[[9,keyindex]][db[[4,keyindex,valind]]]
]

MemDBGet[db_Symbol,indices:{_Integer...}]:=Module[{valind,vals,c2},
	If[Length[indices]==0,Return[{}]];
	Map[Function[{comb},
		c2=MapIndexed[{#2[[1]],#1}&,comb];
		c2=Select[c2,#[[2]]=!=0&];
		(* apply autoapply function before returning the data *)
		Map[Rule[db[[1,#[[1]]]],db[[9,#[[1]]]][db[[4,#[[1]],#[[2]]]]]]&,c2]
		],db[[6,indices]]]
]

MemDBGet[db_Symbol,index_Integer]:=Module[{valind,comb,vals},
	comb=db[[6,index]];
	comb=MapIndexed[{#2[[1]],#1}&,comb];
	comb=Select[comb,#[[2]]=!=0&];
	Map[Rule[db[[1,#[[1]]]],db[[9,#[[1]]]][db[[4,#[[1]],#[[2]]]]]]&,comb]
]

SetAttributes[MemDBSplit,HoldFirst];
MemDBSplit[db_Symbol,samekeys:{_Symbol...},OptionsPattern[]] :=
Module[{ind,keyind},
	keyind=samekeys/.KeyNameDispatch[db];
	If[!And@@((Head[#]===Integer)&/@keyind),
		Message[MemDB::invkey]; Abort[];
	];
	ind=db[[6,1;;db[[7]],keyind]];
	ind=MapIndexed[{#1,#2[[1]]}&,ind];
	ind=ind[[OptionValue[Selection]]];
	ind=Select[ind,!MemberQ[#[[1]],0]&];
	ind=SortBy[ind,#[[1]]&];
	ind=Split[ind,#1[[1]]===#2[[1]]&];
	ind[[All,All,2]]
]

(* split the database into pieces of identical values in "samekeys", iterate over these pieces,
each time evaluating evalexpr with indexvar set to the corresponding indices *)
SetAttributes[MemDBZip,HoldAll];
MemDBZip[db_Symbol,samekeys_,indexvar_Symbol,evalexpr_,OptionsPattern[]]:=
Block[{indexvar},Module[{splitind},
	splitind=MemDBSplit[db,samekeys,Selection->OptionValue[Selection]];
	Map[With[{indexvar=#},evalexpr]&,splitind]
]]

(* used mainly internally to create a new database (dbto) with keys "copykeys" copied from the original database.
No keys are labelled as data keys. *)
SetAttributes[MemDBCopyIndex,HoldFirst];
MemDBCopyIndex[dbfrom_Symbol,dbto_Symbol,copykeys:{_Symbol...}] := 
Module[{keyind},
	keyind=copykeys/.KeyNameDispatch[dbfrom];
	If[!And@@((Head[#]===Integer)&/@keyind),
		Message[MemDB::invkey]; Abort[];
	];
	(* set up the destination data base *)
	dbto=NewMemDB[];
	dbto[[1]]=copykeys;
	dbto[[2]]=Dispatch[MapIndexed[#1->#2[[1]]&,KeyNames[dbto]]];
	dbto[[3]]=dbfrom[[3,keyind]];
	dbto[[4]]=dbfrom[[4,keyind]];
	dbto[[5]]=dbfrom[[5,keyind]];
	dbto[[9]]=dbfrom[[9,keyind]];
	dbto[[10]]=dbfrom[[10,keyind]];
	dbto[[11]]=dbfrom[[11]];
];

(* same as the MemDBZip function above, but this time the result is returned in a data base, and the result obtained from evalexpr is stored in the key given by datakey *)
MemDBZip[db_Symbol,samekeys_,indexvar_Symbol,datakey_Symbol,evalexpr_,OptionsPattern[]]:=
Block[{indexvar},Module[{splitind,keymapping,newdat,keyind,count,keyind2,comb,datkeyind,targetdb,aafcns},
	keyind=samekeys/.KeyNameDispatch[db];
	If[!And@@((Head[#]===Integer)&/@keyind),
		Message[MemDB::invkey]; Abort[];
	];
	splitind=MemDBSplit[db,samekeys,Selection->OptionValue[Selection]];
	MemDBCopyIndex[db,targetdb,samekeys];
	aafcns = OptionValue[AutoApplyFunctions];
	If[aafcns==={},
		datkeyind=datakey/.KeyNameDispatch[db];
		If[!And@@((Head[#]===Integer)&/@keyind),
			Message[MemDB::invkey]; Abort[];
		];	
		MemDBSetDataKey[targetdb,datakey,db[[9,datkeyind]],db[[10,datkeyind]]],
		MemDBSetDataKey[targetdb,datakey,aafcns[[1]],aafcns[[2]]]
	];
	keyind2=samekeys/.KeyNameDispatch[targetdb];
	datkeyind=datakey/.KeyNameDispatch[targetdb];
	count=1;
	Scan[Function[{ind},
		newdat=With[{indexvar=ind},evalexpr];
		(* auto apply function : *)
		newdat=targetdb[[10,datkeyind]][newdat];
		If[count==1,
			targetdb[[4,datkeyind]]=Table[newdat,{Length[splitind]}];
			targetdb[[3,datkeyind]]=Length[splitind];
			targetdb[[6]]=Array[0&,{Length[splitind],Length[keyind2]+1}];
			targetdb[[7]]=Length[splitind];
		];
		targetdb[[4,datkeyind,count]]=newdat;
		targetdb[[6,count,keyind2]]=db[[6,ind[[1]],keyind]];
		targetdb[[6,count,datkeyind]]=count;
		count++;
		],splitind];
	targetdb
]]

SetAttributes[MemDBMap,HoldFirst];
MemDBMap[db_Symbol,datakey_Symbol,fun2arg_,OptionsPattern[]] :=
Module[{indices,datkeyind,copykeys,targetdb,keyind2,datkeyind2,count,olddat,newdat,copykeynames,aafcns},
	datkeyind=datakey/.KeyNameDispatch[db];
	If[!Head[datkeyind]===Integer,
		Message[MemDB::invkey]; Abort[];
	];
	indices=OptionValue[Selection];
	If[indices==All,indices=Range[db[[7]]]];
	indices=Select[indices,db[[6,#,datkeyind]]=!=0&];
	(* copykeys=Complement[Range[Length[KeyNames[db]]],DataKeys[db]]; *)
	copykeys=Complement[Range[Length[KeyNames[db]]],{datkeyind}]; 
	copykeynames=db[[1,copykeys]];
	MemDBCopyIndex[db,targetdb,copykeynames];
	targetdb[[8]]=(KeyNames[db][[Intersection[db[[8]],copykeys]]])/.KeyNameDispatch[targetdb]; (* copy data key property *) 
	aafcns=OptionValue[AutoApplyFunctions];
	If[aafcns==={},
		MemDBSetDataKey[targetdb,datakey,db[[9,datkeyind]],db[[10,datkeyind]]],
		MemDBSetDataKey[targetdb,datakey,aafcns[[1]],aafcns[[2]]]
	];
	keyind2=copykeynames/.KeyNameDispatch[targetdb];
	datkeyind2=datakey/.KeyNameDispatch[targetdb];
	count=1;
	Scan[Function[{ind},
		(* apply autoapply function before returning the data *)
		olddat=db[[9,datkeyind]][db[[4,datkeyind,db[[6,ind,datkeyind]]]]];
		newdat=fun2arg[olddat,ind];
		(* auto apply function : *)
		newdat=targetdb[[10,datkeyind2]][newdat];
		If[count==1,
			targetdb[[4,datkeyind2]]=Table[newdat,{Length[indices]}];
			targetdb[[3,datkeyind2]]=Length[indices];
			targetdb[[6]]=Array[0&,{Length[indices],Length[keyind2]+1}];
			targetdb[[7]]=Length[indices];
		];
		targetdb[[4,datkeyind2,count]]=newdat;
		targetdb[[6,count,keyind2]]=db[[6,ind,copykeys]];
		targetdb[[6,count,datkeyind2]]=count;
		count++;
		],indices];
	targetdb
];

(* does hopefully what you think it does. *)
SetAttributes[MemDBSet,HoldFirst];
MemDBSet[db_Symbol,index_Integer,keyname_Symbol,value_] := 
Module[{keyindex,valueindex},
	keyindex=keyname/.KeyNameDispatch[db];
	If[!Head[keyindex]===Integer,
		Message[MemDB::invkey]; Abort[];
		];
	{keyindex,valueindex}=MemDBGrowValueListI[db,keyindex,value];
	db[[6,index,keyindex]]=valueindex;
];

SetAttributes[MemDBSetGlobals,HoldFirst];
MemDBSetGlobals[db_Symbol,globals_] := 
Module[{keyindex,valueindex},
	db[[11]]=globals;
];

SetAttributes[MemDBGetGlobals,HoldFirst];
MemDBGetGlobals[db_Symbol] := 
Module[{keyindex,valueindex},
	db[[11]]
];

SetAttributes[MemDBListValues,HoldFirst];
Options[MemDBListValues]={Selection->All};
MemDBListValues[db_Symbol,key_Symbol,OptionsPattern[]] := 
Module[{keyindex,valueind},
	keyindex=key/.KeyNameDispatch[db];
	If[!Head[keyindex]===Integer,
		Message[MemDB::invkey]; Abort[];
		];
	valueind=db[[6,1;;db[[7]],keyindex]];
	valueind=valueind[[OptionValue[Selection]]];
	valueind=Select[Union[valueind],#=!=0&];
	(* apply autoapply function before returning the data *)
	db[[9,keyindex]]/@db[[4,keyindex,valueind]]		
];

SetAttributes[MemDBTrimMemory,HoldFirst];
MemDBTrimMemory[db_Symbol] :=
Module[{},
	db[[6]]=db[[6,1;;db[[7]]]];
	MapIndexed[
		(db[[4,#2[[1]]]] = db[[4,#2[[1]],1;;#1]]) &
		,db[[3]]];
	(* Delete value-dispatches; Those can be regenerated : *)
	db[[5]]=Table[{},{Length[KeyNames[db]]}];
];


SetAttributes[MemDBCalcKey,HoldAll];
MemDBCalcKey[db_Symbol,newkey_Symbol,indexvar_Symbol,expr_,OptionsPattern[]] :=
Block[{indexvar},Module[{keyindex,aafcns,indices,dummy,newvalue,pos},
	keyindex=newkey/.KeyNameDispatch[db];
	If[!Head[keyindex]===Integer, (* we have to make a new key *)
		aafcns = OptionValue[AutoApplyFunctions];
		If[TrueQ[OptionValue[DataKey]],
			MemDBSetDataKey[db,newkey],	
			MemDBGrowKeys[db,{newkey}]
			];
		keyindex=newkey/.KeyNameDispatch[db];
		db[[9,keyindex]]=aafcns[[1]];
		db[[10,keyindex]]=aafcns[[2]];
		];
	indices=OptionValue[Selection];
	If[indices==All,indices=Range[db[[7]]]];
	Scan[Function[{ind},
		newvalue=With[{indexvar=ind},expr];
		{dummy,pos}=MemDBGrowValueListI[db,keyindex,newvalue];
		db[[6,ind,keyindex]]=pos;
		],indices];
]];


End[];


EndPackage[];






