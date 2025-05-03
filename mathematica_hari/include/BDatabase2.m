(* ::Package:: *)

BeginPackage["BDatabase2`",{"BIDATEX2`"}]

BDatabaseInit::usage="BDatabaseInit[indexFileName,maxLoadedFiles:5,dataFileNameFcn_:DataFileName] \
	returns a data base which will be read from the files given by <indexFileName> and the \
	function <dataFileName>, which must return a file name for a given integer file number."

MakeDispatch::invkey="Key specification invalid or corrupt lookup table!";
MakeDispatch::usage="used internally.";

Format[BDatabase[args__]]:=StringForm["BDatabase[-files(``)-,classetags->``,subtags->``]",Length[{args}[[5]]],{args}[[6]],{args}[[7]]];

BDBSplitRules::wrongtag="Rules contain unknown tags: `1`";
BDBSplitRules::usage = "Used internally. Split rules into the ones that select the class(=file), and the ones that select the element.";

BDBSelect::nodb="Error: First argument is not a BDatabase object!";
BDBSelect::usage = "BDBSelect[bdb,rules] returns indices for data elements that match the selection criteria given as a list of rules.";

BDBSelectOther::usage="BDBSelectOther[bdb,bdbindex,otherrules] given some indices <bdbindex>, select corresponding entries that have the same \
	specifications except for the ones overridden in <otherrules>.";

BDBGetSpecs::usage="BDBGetSpecs[bdb,bdbindex] show the specifications for the given indices";

BDBGetSpec::wrongtag="Tag `1` does not exist";
BDBGetSpec::usage="BDBGetSpec[bdb,bdbindex,key] show the specifications for the given indices and key.";

BDBGetData::read="Read `` in ``.";
BDBGetData::rearr="Rearranging data access table in ``";
BDBGetData::usage="BDBGetData[bdb,bdbindex] retrieves the data for the given indices.";

BDBConfigToIndex::nfound="Found `1` entries with configuration no. `2`!";
BDBConfigToIndex::usage = "retrieve index in the data blocks corresponding to a given configuration.";
BDBIndexToConfig::usage = "retrieve configuration number corresponding to a position in the data blocks";



BDBListSpecs::usage="BDBListSpecs[bdb,key] list the different values that the given key takes on in throughout the data base";

BDBCommonSpecs::usage="BDBCommonSpecs[bdb,bdbindex] lists specifications that agree among the entries specified in <bdbindex>";

BDBCommonSpec::nunique:="No common content for tag ``!";

BDBCommonSpec::usage="BDBCommonSpec[bdb,bdbindex,key] lists the common value that the key <key> takes on for the entries
	specified in <bdbindex>. Aborts if the values differ."


BDBIndexToList::usage = "BDBIndexToList[bdbindex] converts a BDBIndex to a list in which every element specifies a data base entry uniquely \
	as a (file index,entry index) pair.";

ListToBDBIndex::usage = "ListToBDBIndex[indlist] reverse functionality as BDBIndexToList";

NumElements::usage = "NumElements[ind] gives the number of entries specified by the BDBIndex <ind>.";


sublookups::usage = "internally used in the BDatabase format";
classlookup::usage = "internally used in the BDatabase format";
symboltable::usage = "internally used in the BDatabase format";
keytable::usage = "internally used in the BDatabase format";

BDBIndex::usage = "Labels data base indices in the BDatabase framework.";




Begin["`Private`"];

DataFileName[n_Integer,bdb_BDatabase]:=(outputfiles/.(globals/.bdb[[1]]))[[n+1]];

BDatabaseInit[indexFileName_,maxLoadedFiles_:5,dataFileNameFcn_:DataFileName]:=Module[{res},
	res=BIDATEXReader[indexFileName];
	BDatabase[
		res, (* 1: Index *)
		dataFileNameFcn, (* 2: DataFileName *)
		{}, (* 3: Class-Dispatches *)
		Table[{},{Length[sublookups/.res]}], (* 4: Sub-Dispatches *)
		{}, (* 5: Buffers *)
		(symboltable/.(classlookup/.res))[[All,1]], (* 6: Class-Tags *)
		(symboltable/.res)[[All,1]], (* 7: Sub-Tags *)
		maxLoadedFiles (* 8: MaxLoadedFiles *)
	]
];


MakeDispatch[keytab_,symtab_,allkeys_,keys_:All]:=Module[{mselkeys,savselkeys,tab},
	mselkeys = If[keys===All,allkeys,keys];
	If[Head[mselkeys]=!=List,Message[MakeDispatch::invkey]; Abort[]];
	savselkeys=Union[mselkeys];
	If[Length[mselkeys]=!=Length[savselkeys],Message[MakeDispatch::invkey];Abort[]];
	mselkeys = Map[Position[allkeys,#]&,savselkeys,{1}];
	mselkeys=Flatten/@mselkeys;
	If[!And@@((Length[#]==1&)/@mselkeys),Message[MakeDispatch::invkey];Abort[]];
	mselkeys=mselkeys[[All,1]];
	tab=MapIndexed[Function[{k,n},
	Map[symtab[[#,2,k[[#]]+1]]&,mselkeys]->n[[1]]
	 ],keytab];
	tab=SortBy[tab,#[[1]]&];
	tab=Split[tab,#1[[1]]===#2[[1]]&];
	tab=Map[#[[1,1]]->BDBKeys@@#[[All,2]]&,tab];
	savselkeys->Dispatch[tab]
];


BDBSplitRules[rules_List,classtags_,subtags_]:=Module[{classrules,subrules,rules2,tmp},
	rules2=SortBy[rules,#[[1]]&];
	classrules=Intersection[rules2,classtags,SameTest->(#1[[1]]===#2 &)];
	subrules=Complement[rules2,classtags,SameTest->(#1[[1]]===#2 &)];
	tmp=Complement[subrules,subtags,SameTest->(#1[[1]]===#2 &)];
	If[Length[tmp]>0,Message[BDBSplitRules::wrongtag,tmp];Abort[]];
	{classrules,subrules}
];

SetAttributes[BDBSelect,HoldFirst];
BDBSelect[bdb_,rules_List]:=Module[{rules2,classrules,subrules, classkeys,subkeys,tmp,res},
	If[Head[bdb]=!=BDatabase,Message[BDBSelect::nodb];Abort[]];
	{classrules,subrules}=BDBSplitRules[rules,bdb[[6]],bdb[[7]]];
	(* we have now classrules and subrules available to do the selection *)
	tmp=classrules[[All,1]]/.bdb[[3]];
	If[tmp===classrules[[All,1]],
		tmp=MakeDispatch[keytable/.(classlookup/.bdb[[1]]),symboltable/.(classlookup/.bdb[[1]]),bdb[[6]],tmp];
		AppendTo[bdb[[3]],tmp];
		tmp=tmp[[2]];
	];
	classkeys=classrules[[All,2]]/.tmp;
	If[Head[classkeys]=!=BDBKeys,Return[{}]]; (* not found *)
	res=List@@Map[Function[{ck},
		tmp=subrules[[All,1]]/.bdb[[4,ck]];
		If[tmp===subrules[[All,1]],
			tmp=MakeDispatch[(keytable/.(sublookups/.bdb[[1]]))[[ck]],symboltable/.bdb[[1]],bdb[[7]],tmp];
			AppendTo[bdb[[4,ck]],tmp];
			tmp=tmp[[2]];
		];
		subkeys=subrules[[All,2]]/.tmp;
		If[Head[subkeys]=!=BDBKeys,subkeys=BDBKeys[]];
		{ck,subkeys}
		],classkeys];
	res=Select[res,Length[#[[2]]]>0&];
	BDBIndex@@Map[{#[[1]],List@@#[[2]]}&,res]
];

(* fast only for a great number of elements in bdbindex *)
SetAttributes[BDBSelectOther,HoldFirst];
BDBSymtabToIndx::invsel="Selection criteria invalid";
BDBSymtabToIndx[symtab_,rules_]:=Module[{subs},
	subs=Map[Position[symtab[[All,1]],#[[1]]][[1,1]]&,rules];
	subs={subs,Map[Position[#[[1]]/.symtab,#[[2]]]&,rules]};
	If[Min[Length/@subs[[2]]]==0,Message[BDBSymtabToIndx::invsel];Abort[]];
	subs[[2]]=subs[[2,All,1,1]];
	subs
];
BDBSelectOther[bdb_,bdbindex_BDBIndex,otherrules_List]:=Module[{classrules,subrules,csubs,ssubs,keys,disp,resindx,keytab},
	If[Head[bdb]=!=BDatabase,Message[BDBSelect::nodb];Abort[]];
	{classrules,subrules}=BDBSplitRules[otherrules,bdb[[6]],bdb[[7]]];
	csubs=BDBSymtabToIndx[symboltable/.(classlookup/.bdb[[1]]),classrules];
	ssubs=BDBSymtabToIndx[symboltable/.bdb[[1]],subrules];
	(* Let's apply csubs, the class keys *)
	keys=(keytable/.(classlookup/.bdb[[1]]))[[List@@bdbindex[[All,1]]]];
	keys[[All,csubs[[1]]]]=Table[csubs[[2]]-1,{Length[keys]}];
	disp=BDBKeys/.bdb[[3]];
	If[disp===BDBKeys,
		disp=Dispatch[MapIndexed[#1-> #2[[1]]&,keytable/.(classlookup/.bdb[[1]])]];
		AppendTo[bdb[[3]],BDBKeys->disp];
	];
	resindx=bdbindex;
	resindx[[All,1]]=keys/.disp;
	(* Let's apply ssubs, the sub keys *)
	Map[Function[{i},
		keytab=keytable/.(sublookups/.bdb[[1]])[[i[[1]]]];
		keys=keytab[[i[[2]]]];
		keys[[All,ssubs[[1]]]]=Table[ssubs[[2]]-1,{Length[keys]}];
		disp=BDBKeys/.bdb[[4,i[[1]]]];
		If[disp===BDBKeys,
			disp=Dispatch[MapIndexed[#1-> #2[[1]]&,keytab]];
			AppendTo[bdb[[4,i[[1]]]],BDBKeys->disp];
		];
		{i[[1]],keys/.disp}
	],resindx]
];

(* optimized for speed! *)
BDBGetSpecs[bdb_BDatabase,bdbindex_BDBIndex]:=Module[{i,ckeys,skeys,ckeytab,csymtab,skeytab,skeytabs,ssymtab},
	ckeytab=(keytable/.(classlookup/.bdb[[1]]));
	csymtab=(symboltable/.(classlookup/.bdb[[1]]));
	ssymtab=(symboltable/.bdb[[1]]);
	skeytabs=(keytable/.(sublookups/.bdb[[1]]));
	Flatten[List@@Map[Function[{i},
		ckeys=ckeytab[[i[[1]]]]+1;
		ckeys=MapThread[#2[[1]]->#2[[2,#1]]&,{ckeys,csymtab}];
		skeytab=skeytabs[[i[[1]]]];
		Map[Function[{j},
			skeys=skeytab[[j]]+1;
			skeys=MapThread[#2[[1]]->#2[[2,#1]]&,{skeys,ssymtab}];
			Select[Join[ckeys,skeys],#[[2]]=!=Nothing&]
		],i[[2]]]
	],bdbindex],1]
]

(* optimized for speed! *)
BDBGetSpec[bdb_BDatabase,bdbindex_BDBIndex,tag_]:=Module[{pos,inclass,i,el,keytab,symtab,keytabs},
	pos=Position[bdb[[6]],tag];
	inclass=True;
	If[Length[pos]===0,inclass=False;pos=Position[bdb[[7]],tag]];
	If[Length[pos]===0,Message[BDBGetSpec::wrongtag,tag]; Abort[]];
	pos=pos[[1,1]];
	If[inclass,
		keytab=(keytable/.(classlookup/.bdb[[1]]));
		symtab=(symboltable/.(classlookup/.bdb[[1]]))[[pos,2]],
		symtab=(symboltable/.bdb[[1]])[[pos,2]];
		keytabs=(keytable/.(sublookups/.bdb[[1]]));
	];
	Flatten[List@@Map[Function[{i},
		If[inclass,
			el=symtab[[keytab[[i[[1]],pos]]+1]],
			keytab=keytabs[[i[[1]],All,pos]];
		];
		Map[Function[{j},
			If[inclass,
				el,
				symtab[[keytab[[j]]+1]]
			]
		],i[[2]]]
	],bdbindex],1]
]

(* This implementation is faster if the buffer never becomes full. *)
SetAttributes[BDBGetData2,HoldFirst];
BDBGetData2[bdb_,bdbindex_BDBIndex]:=Module[{i,fname,dat,tim},
	If[Head[bdb]=!=BDatabase,Message[BDBSelect::nodb];Abort[]];
	Flatten[List@@Map[Function[{i},
		dat=i[[1]]/.bdb[[5]];
		If[dat===i[[1]],
			fname=bdb[[2]][i[[1]]-1,bdb];
			tim=Timing[dat=BIDATEXReader[fname];][[1]];
			Message[BDBGetData::read,fname,tim];
			If[Length[bdb[[5]]]>=bdb[[8]],bdb[[5]]=Rest[bdb[[5]]]];
			AppendTo[bdb[[5]],i[[1]]->dat];
		];
		dat[[i[[2]]]]
	],bdbindex],1]
]


(* This implementation rearranges the buffer in such a way that file contents
accessed lately come later in the buffer, so that they are not deleted right away;
Rearrangement takes a tiny bit of time. *)
SetAttributes[BDBGetData,HoldFirst];
BDBGetData[bdb_,bdbindex_BDBIndex]:=Module[{i,sel,fname,dat,tim,rearrlist},
	If[Head[bdb]=!=BDatabase,Message[BDBSelect::nodb];Abort[]];
	Flatten[List@@Map[Function[{i},
		sel=Position[bdb[[5,All,1]],i[[1]]];
		If[Length[sel]>0,
			sel=sel[[1,1]];
			dat=bdb[[5,sel]];
			bdb[[5]]=Append[Delete[bdb[[5]],sel],dat];
			(*Message[BDBGetData::rearr,tim];*)
			dat=dat[[2]],
			fname=bdb[[2]][i[[1]]-1,bdb];
			tim=Timing[dat=BIDATEXReader[fname];][[1]];
			Message[BDBGetData::read,fname,tim];
			If[Length[bdb[[5]]]>=bdb[[8]],bdb[[5]]=Rest[bdb[[5]]]];
			AppendTo[bdb[[5]],i[[1]]->dat]
		];
		dat[[i[[2]]]]
	],bdbindex],1]
]


BDBIndexToConfig[bdb_BDatabase,i_Integer]:=StringSplit[(inputfiles/.(globals/.bdb[[1]]))[[i]],"."][[-2]];


BDBConfigToIndex[bdb_BDatabase,cfg_Integer]:=Module[{cfgs,pos},
	cfgs=Map[StringSplit[#,"."][[-2]]&,(inputfiles/.(globals/.bdb[[1]]))];
	pos=Position[cfgs,ToString[cfg]];
	If[Length[pos]=!=1,Message[BDBConfigToIndex::nfound,Length[pos],cfg]; Abort[]];
	pos[[1,1]]
]


BDBConfigToIndex[bdb_BDatabase,cfgs_List]:=Module[{acfgs,pos},
	acfgs=Map[StringSplit[#,"."][[-2]]&,(inputfiles/.(globals/.bdb[[1]]))];
	Map[Function[{cfg},
		pos=Position[acfgs,ToString[cfg]];
		If[Length[pos]=!=1,Message[BDBConfigToIndex::nfound,Length[pos],cfg]; Abort[]];
		pos[[1,1]]
	],cfgs]
]


BDBListSpecs[bdb_BDatabase,tag_]:=Module[{res},
	res=tag/.(symboltable/.(classlookup/.bdb[[1]]));
	If[res===tag,res=tag/.(symboltable/.bdb[[1]])];
	If[res===tag,Return[{}]];
	DeleteCases[res,Nothing]
]


BDBCommonSpecs[bdb_BDatabase,bdbindex_BDBIndex]:=Module[{keys,sel,tmp,res,keytab},
	If[Length[bdbindex]==0,Return[{}]];
	keys=(keytable/.(classlookup/.bdb[[1]]))[[List@@bdbindex[[All,1]]]]+1;
	sel=SameQ@@#&/@Transpose[keys];
	tmp=Pick[symboltable/.(classlookup/.bdb[[1]]),sel];
	keys=Pick[keys[[1]],sel];
	res=MapThread[#1[[1]]->#1[[2,#2]]&,{tmp,keys}];
	keytab=(keytable/.(sublookups/.bdb[[1]]));
	keys=Flatten[List@@Map[keytab[[#[[1]],#[[2]]]]+1&,bdbindex],1];
	sel=SameQ@@#&/@Transpose[keys];
	tmp=Pick[symboltable/.bdb[[1]],sel];
	keys=Pick[keys[[1]],sel];
	res=Join[res,MapThread[#1[[1]]->#1[[2,#2]]&,{tmp,keys}]];
	Select[res,#[[2]]=!=Nothing &]
];


(* optimized for speed! *)
BDBCommonSpec::nunique:="No common content for tag ``!";
BDBCommonSpec[bdb_BDatabase,bdbindex_BDBIndex,tag_]:=Module[{pos,inclass,i,el,keytab,symtab,keytabs},
	pos=Position[bdb[[6]],tag];
	inclass=True;
	If[Length[pos]===0,inclass=False;pos=Position[bdb[[7]],tag]];
	If[Length[pos]===0,Message[BDBGetSpec::wrongtag,tag]; Abort[]];
	pos=pos[[1,1]];
	If[inclass,
		keytab=(keytable/.(classlookup/.bdb[[1]]));
		symtab=(symboltable/.(classlookup/.bdb[[1]]))[[pos,2]];
		el=Flatten[List@@Map[Function[{i},keytab[[i[[1]],pos]]+1],bdbindex],1],
		symtab=(symboltable/.bdb[[1]])[[pos,2]];
		keytabs=(keytable/.(sublookups/.bdb[[1]]));
		el=Flatten[List@@Map[Function[{i},
		keytab=keytabs[[i[[1]],All,pos]];
		Map[Function[{j},keytab[[j]]+1],i[[2]]]
			],bdbindex],1];
		];
	If[SameQ@@el, symtab[[el[[1]]]], Message[BDBCommonSpec::nunique, tag]; tag]
]


BDBIndexToList[bdbindex_BDBIndex]:=Flatten[List@@Map[Function[{i},Map[{i[[1]],#}&,i[[2]]]],bdbindex],1];

ListToBDBIndex[indlist_]:=BDBIndex@@Map[{#[[1,1]],#[[All,2]]}&,Split[indlist,#1[[1]]==#2[[1]]&]];

NumElements[ind_BDBIndex]:=Plus@@Map[Length[#[[2]]]&,ind];

End[];

EndPackage[];
