(* ::Package:: *)

BeginPackage["Resampling3`"];

ErrorBounds::usage="Tags error intervals.";
ErrorBoundsRel::usage="Tags values with errors.";
StdErrorBounds::usage="Converts to ErrorBoundsRel in standardized form.";
CentralErrorBounds::usage="Converts to ErrorBoundsRel, the value centered in the error interval";
CentralErrorBounds2::usage="Converts to ErrorBoundsRel with a single error bound, averaged from upper and lower errors.";
ErrForm::usage="Display errors nicely.";
ErrFormExp::usage="Display errors nicely, optimized for export.";
ErrFormTex::usage="Display errors in tex compatible form";
ErrPrint::usage="Print a value with an error";

StrucThread::usage="Combine into one head.";
StrucUnThread::usage="Split structures onto several heads.";
NoOutliersEstimator::usage="Estimator which neglects outliers.";

JacknifeSamples::usage="Tags Jacknife samples.";
JacknifeRescaling::usage="obsolete";
MakeJacknifeSamples::usage="Form Jacknife Samples from the data";
JacknifeStatistics::usage="Calculate Jacknife Errors";
ResamplingFit::usage="Fit to Jacknife data";
JacknifeFit::usage="Fit to Jacknife data";
JacknifePlot::usage="Obsolete: Plot error band from Jacknife data";
ResamplingPlot::usage="Plot error band from Jacknife/Bootstrap data";
JacknifeCombine::usage="For advanced user: combine Jacknife samples of different lengths";

ResamplingDataType::usage="Determine type of samples (returns BootstrapSamples or JacknifeSamples).";

RealQ::usage="RealQ[x] Returns True if x is an explicit real number.";

Options[JacknifeStatistics]=Sort[{
	Autocorr->True,
	NoNegativeAutocorr->True,
	Verbose->True
	}];

Options[ResamplingFit]=Sort[{
	FitWeights->Automatic,
	AdjustStartValues-> True,
	NumSamples->All
	}];

Options[ResamplingPlot]=Sort[{
	GiveVertices->False
	}];

Options[JacknifeRescaling]=Sort[{
	BlockSize->1,
	FastRescaling->False,
	Estimator->(Total[#]/Length[#]&)
	}];

Options[AutocorrSummary] = {
	ACMethod->Normal
	};


MakeBootstrapSampler::usage="Help.";
MakeBootstrapSamplerSellist::usage="MoreHelp.";
BootstrapSamples::usage="Tags bootstrap samples.";
BootstrapStatistics::usage="Calculate Error intervals.";
WithSamples::usage="Apply substitution rules <Symbol>-><Value>, where <Value> can be samples.";

Options[CreateBootstrapSampler] = {
	BinSize->1,
	Estimator->Mean,
	NumSamples->1000
	};

Options[MakeBootstrapSampler] := Options[CreateBootstrapSampler];


Options[BootstrapStatistics]={
	ConfidenceLevel->0.68269
	};

ResamplingStatistics::usage="Calculate errors.";

Unprotect[Indeterminate];
Format[Indeterminate]="\!\(\*
StyleBox[\"??\",\nFontSlant->\"Italic\"]\)";
Protect[Indeterminate];


Begin["`Private`"];

(*********************** GENERAL TOOLS ************************)

RealQ[xseq__]:=And@@(TrueQ[Element[#,Reals]]&/@{xseq});

StrucThread[head_Symbol,a_List]:=
Module[{l,n},
	l=StrucThread[head,#]&/@a;
	If[And@@((Head[#]===head)&/@l),
		If[SameQ@@(Length/@l),
			head@@Transpose[List@@#&/@l],
			l],
		l
		]
	];
StrucThread[head_Symbol,a_]:=a; 

StrucUnThread[head_Symbol,a_List] := Map[StrucUnThread[head,#]&,a];
StrucUnThread[head_Symbol,a_] := 
	If[Head[a]===head,
		Module[{t,d},
			d=ArrayDepth[List@@a]+1;
			If[Length[a]<1 ||  d<3,Return[a]];
			MapIndexed[StrucUnThread[head,a[[All,Sequence@@#2]]]&,a[[1]]]
			],
		a
	];

Unravel[head_Symbol,l_] := 
Module[{},
	If[Head[l]===List,Return[Unravel[head,#]&/@l]];
	If[Head[l]=!=head,Return[l]];
	If[!And@@(Head[#]===List &/@l),Return[l]];
	If[!SameQ@@(Length/@l),Return[l]];
	Map[Unravel[head,head@@#]&,Transpose[List@@l]]
	];

StdErrorBounds[ErrorBounds[c_,{l_,u_}]]:=ErrorBoundsRel[c,{If[RealQ[l,c],Min[l-c,0],Indeterminate],If[RealQ[u,c],Max[u-c,0],Indeterminate]}];
StdErrorBounds[ErrorBoundsRel[c_,pm_]]:=ErrorBoundsRel[c,If[RealQ[pm],{-pm,pm},{Indeterminate,Indeterminate}]];
StdErrorBounds[ErrorBoundsRel[c_,{l_,u_}]]:=ErrorBoundsRel[c,{l,u}];
StdErrorBounds[x_]:=(x/.{e_ErrorBounds:>StdErrorBounds[e],e_ErrorBoundsRel:>StdErrorBounds[e]});

CentralErrorBounds[ErrorBounds[c_,{l_,u_}]] := ErrorBoundsRel[Sequence@@If[RealQ[l,u],{Mean[{l,u}],Abs[u-l]/2},{c,Indeterminate}]];
CentralErrorBounds[ErrorBoundsRel[c_,{l_,u_}]] := ErrorBoundsRel[Sequence@@If[RealQ[l,u,c],{c+Mean[{l,u}],Abs[u-l]/2},{c,Indeterminate}]];
CentralErrorBounds[ErrorBoundsRel[c_,pm_]] := ErrorBoundsRel[c,pm];
CentralErrorBounds[x_]:=(x/.{e_ErrorBounds:>CentralErrorBounds[e],e_ErrorBoundsRel:>CentralErrorBounds[e]});

(* same as above, but take the "central value" unaltered from the ErrorBounds[] *)
CentralErrorBounds2[ErrorBounds[c_,{l_,u_}]] := ErrorBoundsRel[Sequence@@If[RealQ[l,u],{c,Abs[u-l]/2},{c,Indeterminate}]];
CentralErrorBounds2[ErrorBoundsRel[c_,{l_,u_}]] := ErrorBoundsRel[Sequence@@If[RealQ[l,u,c],{c,Abs[u-l]/2},{c,Indeterminate}]];
CentralErrorBounds2[ErrorBoundsRel[c_,pm_]] := ErrorBoundsRel[c,pm];
CentralErrorBounds2[x_]:=(x/.{e_ErrorBounds:>CentralErrorBounds2[e],e_ErrorBoundsRel:>CentralErrorBounds2[e]});

NoOutliersEstimator[x_List,p_:0.68269]:=Module[{n,k},
	n=Floor[(Length[x]-Floor[Length[x]*p])/2];
	If[Length[x]<=2*n,Return[Median[x]]];
	Mean[Take[Sort[x],{1+n,Length[x]-n}]]
	];

ChiSqrThresh[n_,CL_] := x /.Solve[CDF[ChiSquareDistribution[n],x]==CL,x][[1]]

ErrPrint[val_,err_,pmstr_:"\[ThinSpace]\[PlusMinus]\[ThinSpace]",mulstr_:"\[ThinSpace]\[Times]\[ThinSpace]",supersc_:(Superscript["10",#]&)] := 
Module[{mee,mev,eshift,errint,valint,decpt,padr,vexp,valstr,errstr,res},
	mev=MantissaExponent[val];
	If[mev[[1]]==0,Return[StringForm["0"<>pmstr<>"``",NumberForm[err,2]]]];
	mee=MantissaExponent[err];
	If[mee[[1]]==0,Return[StringForm["``",NumberForm[val,2]]]];
	If[mev[[2]]-mee[[2]]<-2,Return[StringForm["0"<>pmstr<>"``",NumberForm[err,2]]]];
	If[mev[[2]]<mee[[2]],Return[StringForm["``"<>pmstr<>"``",NumberForm[val,1],NumberForm[err,2]]]];
	eshift=2-mee[[2]];
	errint=Ceiling[err*10^eshift];
	errstr=ToString/@IntegerDigits[errint];
	eshift-=Length[errstr]-2;errstr=errstr[[{1,2}]];
	valint=Round[val*10^eshift];
	mev=MantissaExponent[valint*10^(-eshift)];
	vexp=If[-3<mev[[2]]<=3,0,3*Floor[(mev[[2]]-1)/3]];
	decpt=mev[[2]]-vexp;
	valstr=ToString/@IntegerDigits[valint];
	If[decpt<=0,
		valstr=Join[Table["0",{1-decpt}],valstr];
		decpt=1
		];
	padr=decpt-Length[valstr];
	If[padr>0,valstr=Join[valstr,Table["0",{padr}]];
	errstr=Join[errstr,Table["0",{padr}]]];
	If[decpt>0&&Length[valstr]-decpt>0,valstr=Insert[valstr,".",decpt+1]];
	res=If[Sign[valint]==-1,"-",""]<>StringJoin@@valstr<>"("<>StringJoin@@errstr<>")";
	If[vexp!=0,res=StringForm["``"<>mulstr<>"``",res,supersc[ToString[vexp]]]];
	res
	];

ErrPrint[val_,errs_List,pmstr_:"\[ThinSpace]\[PlusMinus]\[ThinSpace]",mulstr_:"\[ThinSpace]\[Times]\[ThinSpace]",supersc_:(Superscript["10",#]&)] := 
Module[{mee,mev,eshift,errint,valint,decpt,padr,vexp,valstr,errstr,res,errcol},
	If[!RealQ[val],Return[val]];
	mev=MantissaExponent[val];
	errcol:=Style[Column[NumberForm[#,2,NumberSigns->{"-","+"}]&/@Reverse[errs],Right,0],Small];
	If[!(And@@(RealQ/@errs)),Return[StringForm["````",val,errcol]]];
	If[mev[[1]]==0,Return[StringForm["0"<>"``",errcol]]];
	mee=MantissaExponent[Max[Abs[errs]]];
	If[mee[[1]]==0,Return[StringForm["``",NumberForm[val,2]]]];
	If[mev[[2]]-mee[[2]]<-2,Return[StringForm["0"<>"``",errcol]]];
	If[mev[[2]]<mee[[2]],Return[StringForm["``"<>"``",NumberForm[val,1],errcol]]];
	eshift=2-mee[[2]];
	errint=Ceiling/@(Abs[errs]*10^eshift);
	errstr=Map[ToString,IntegerDigits/@errint,{2}];
	errstr=Map[PadLeft[#,Max[Length/@errstr],"0"]&,errstr];
	eshift-=Length[errstr[[1]]]-2;
	errstr=errstr[[All,{1,2}]];
	valint=Round[val*10^eshift];
	mev=MantissaExponent[valint*10^(-eshift)];
	vexp=If[-3<mev[[2]]<=3,0,3*Floor[(mev[[2]]-1)/3]];
	decpt=mev[[2]]-vexp;
	valstr=ToString/@IntegerDigits[valint];
	If[decpt<=0,
		valstr=Join[Table["0",{1-decpt}],valstr];
		decpt=1
		];
	padr=decpt-Length[valstr];
	If[padr>0,valstr=Join[valstr,Table["0",{padr}]]];
	errstr=Map[Join[#,Table["0",{padr}]]&,errstr];
	errstr=MapThread[Join[{"(",Which[#2>0,"+",#2<0,"-",#3==1,"-",True,"+"]},#1,{")"}]&,{errstr,errs,Range[Length[errs]]}];
	If[decpt>0&&Length[valstr]-decpt>0,valstr=Insert[valstr,".",decpt+1]];
	res=Row[{If[Sign[valint]==-1,"-",""],StringJoin@@valstr,Style[Column[Reverse[StringJoin/@errstr],Center,0],Small]}];
	If[vexp!=0,res=StringForm["``"<>mulstr<>"``",res,supersc[ToString[vexp]]]];
	res
	];

ErrForm[x_]:=x/.{ErrorBoundsRel[val_,err_]:>ErrPrint[val,err]};
ErrFormExp[x_]:=x/.{ErrorBoundsRel[val_,err_]:>ErrPrint[val,err,"+-","*",("10^"<>#&)]};
ErrFormTex[x_]:=x/.{ErrorBoundsRel[val_,err_]:>ErrPrint[val,err," \\pm "," \\times ", ("10^{"<>#<>"}" &)]};


(*********************** Jacknife Statistics ************************)

MakeBlocks::ndivisible="List length should be divisible by `1`.";
MakeBlocks[l_List,n_Integer] := If[Mod[Length[l],n]==0,Mean/@Partition[l,n],Message[MakeBlocks::ndivisible,n]];

AutocorrAux[l_List,k_Integer] := Total[Drop[l,-k]*Drop[l,k]]/(Length[l]-1-k);
AutocorrAux2[l_List,k_Integer] := 
Module[{L,R},
	L=Drop[l,-k]; R=Drop[l,k];
	(Total[L*R]-Total[L]*Total[R])/(Length[l]-1-k)
	];

Autocorr[l_List,k_Integer] := 
Module[{l2,nrm},
	l2=l-Mean[l];
	nrm=AutocorrAux[l2,0];
	If[nrm!=0,AutocorrAux[l2,k]/nrm,0]
	];

Autocorr2[l_List,k_Integer] :=
Module[{l2,nrm},
	l2=l-Mean[l];
	nrm=AutocorrAux2[l2,0];
	If[nrm!=0,AutocorrAux2[l2,k]/nrm,0]
	]

AutocorrFourier[l_List] := 
Module[{ft,res},
	ft=Fourier[l-Mean[l]];
	res=Fourier[ft*Conjugate[ft]];
	If[res[[1]]!=0,res/res[[1]],PadRight[{1},Length[l]]]
	];

AutocorrSummary::inacc="Warning! Estimated autocorrelation time inaccurate!";

AutocorrSummaryAux[l_List,autocorrfn_] := 
Module[{n,l2,nrm,k,autol,taui2},
	n=Length[l]; 
	l2=l-Mean[l]; 
	nrm=autocorrfn[l2,0];
	If[nrm==0,Return[{0,1,{1}}]];
	k=1; 
	autol={1,Autocorr2[l2,k]/nrm};
	taui2=(1-k/n)*Last[autol];
	While[k<n-2 && k<6(taui2+1/2),
		k++; 
		AppendTo[autol,autocorrfn[l2,k]/nrm]; 
		taui2+=(1-k/n)*Last[autol];
		];
	{taui2,k,autol}
	];

AutocorrSummaryAuxFourier[l_List] := 
Module[{n,nu,k,autol,taui2},
	n=Length[l]; 
	autol=AutocorrFourier[l];
	nu=Floor[n/2];
	k=1; 
	taui2=autol[[k+1]];
	While[k<n-2 && k<nu && k<6(taui2+1/2),
		k++; 
		taui2+=autol[[k+1]];
		];
	{taui2,k,autol}
	];

AutocorrSummary::bdopts="Invalid option `1`";
AutocorrSummary[l_List,opts___?OptionQ] := Module[{k,taui,taui2,b,autol,tauierr,optmeth},
	{optmeth}={ACMethod}/.Flatten[{opts,Options[AutocorrSummary]}];
	Switch[optmeth,
		Normal,{taui2,k,autol}=AutocorrSummaryAux[l,Autocorr],
		Unbiased,{taui2,k,autol}=AutocorrSummaryAux[l,Autocorr2],
		Fourier,{taui2,k,autol}=AutocorrSummaryAuxFourier[l],
		_,Message[AutocorrSummary::bdopts,Method->optmeth]; Abort[]
		];
	taui=taui2+1/2;
	tauierr=Abs[taui]*Sqrt[2(2k+1)/Length[l]];
	If[tauierr>Abs[taui]/3,Message[AutocorrSummary::inacc]];
	b=taui2/(1+taui2);
	{
		IntACTime->taui,
		IntACTimeError->tauierr,
		DecayConst->b,
		ACSampleLength->k,
		Autocorrelations->autol
		}
	];

JacknifeSamples/:Plus[a_JacknifeSamples,x__JacknifeSamples]:=JacknifeSamples@@MapThread[Plus,List@@#&/@{a,x}];
JacknifeSamples/:Times[a_JacknifeSamples,x__JacknifeSamples]:=JacknifeSamples@@MapThread[Times,List@@#&/@{a,x}];
JacknifeSamples/:x_JacknifeSamples*c_?NumericQ:=JacknifeSamples@@(List@@x*c);
JacknifeSamples/:x_JacknifeSamples^c_?NumericQ:=JacknifeSamples@@(List@@x^c);

MakeJacknifeSamples::indivisible="Error: Data length not divisible by blocksize ``!";
MakeJacknifeSamples::short="Cannot create Jacknife dataset from 0 or 1 element!";
MakeJacknifeSamples[data_List,blocksize_Integer:1,estimator_:Default] := 
Module[{tot,div,pdat,k},
	If[Mod[Length[data],blocksize]=!=0 || Length[data]<blocksize,Message[MakeJacknifeSamples::indivisible,blocksize]; Abort[]];
	If[blocksize>1,
		pdat=(Total/@Partition[data,blocksize])/blocksize,
		pdat=data;
		];
	If[Length[pdat]<2,Message[MakeJacknifeSamples::short];Return[pdat]];
	If[estimator===Default,
		tot=Total[pdat];
		JacknifeSamples@@Prepend[Map[tot-#&,pdat]/(Length[pdat]-1),tot/Length[pdat]],
		pdat=StrucUnThread[JacknifeSamples,JacknifeSamples@@pdat];
		Map[(
			tot=estimator[List@@#];
			JacknifeSamples@@Prepend[Table[estimator[List@@Delete[#,k]],{k,Length[#]}],tot]
			)&,pdat,{ArrayDepth[pdat]}]
		]
	];

(* JacknifeRescaling is obsolte! *)

JacknifeRescaling::bdopts="Invalid option `1`";
JacknifeRescaling::incomp="Incompatible options: Custom Estimator not possible for FastRescaling";
JacknifeRescaling[data_List,opts___?OptionQ] := 
Module[{blocksize,optfast,tot,blks,res},
	{blocksize,optfast,est}={BlockSize,FastRescaling,Estimator}/.Flatten[{opts,Options[JacknifeRescaling]}];
	If[Mod[Length[data],blocksize]=!=0,Message[MakeBlocks::ndivisible,blocksize]; Abort[]];
	If[Length[data]/blocksize<2,Return[{est[data]}]];
	If[FastRescaling->True && Estimator=!=(Estimator/.Options[JacknifeRescaling]),
		Message[JacknifeRescaling::incomp]; Abort[]];
		res=Switch[optfast,
			False,Table[est[Drop[data,{k,k+blocksize-1}]],{k,Length[data]-blocksize+1,1,-blocksize}],
			True, tot=Total[data]; blks=If[blocksize>1,Total/@Partition[data,blocksize],data]; Reverse[Map[tot-#&,blks]/(Length[data]-blocksize)],
			_,Message[JacknifeRescaling::bdopts,FastRescaling->optfast]; Abort[]];
	JacknifeSamples@@Prepend[res,est[data]]
	];





StudentFactor[nsamp_]:=N[InverseCDF[StudentTDistribution[nsamp],CDF[NormalDistribution[0,1],1]]]

JacknifeStatistics::bdopts="Invalid option `1`";
JacknifeStatistics[jacknifeestimates_List,opts___?OptionQ] := Map[JacknifeStatistics[#,opts]&,jacknifeestimates];
JacknifeStatistics[jacknifeestimates_JacknifeSamples,opts___?OptionQ] := 
Module[{optac,optnegat,optverb,je,ac,actfac,cent,centj,ssq,jackvar,err,ret,n,c,jacked,studfac},
	{optac,optnegat,optverb}={Autocorr,NoNegativeAutocorr,Verbose}/.Flatten[{opts,Options[JacknifeStatistics]}];
	je=StrucUnThread[JacknifeSamples,jacknifeestimates];
	If[Head[je]=!=JacknifeSamples,Return[JacknifeStatistics[je,opts]]];
	n=Length[je]-1;
	c=je[[1]];
	jacked=Rest[List@@je];
	If[n<2,Return[{ErrorBoundsRel[c,Indeterminate],{}}]];
	centj=Mean[jacked];
	bias=(n-1)(centj-c);
	cent=c-bias;
	ssq=Total[(jacked-centj)^2];
	jackvar=ssq *(n-1)/n;
	studfac=StudentFactor[n];
	ret={
		SampleEstimate->c,
		SampleVariance->(n-1)ssq,
		Bias->bias,
		JacknifeVariance->jackvar,
		JacknifeError->Sqrt[jackvar]*studfac
		};
	ac=Switch[optac,
		False,{},
		True,AutocorrSummary[jacked,Sequence@@FilterRules[{opts},Options@AutocorrSummary]],
		_,Message[JacknifeStatistics::bdopts,Autocorr->optac]; Abort[]
		];
	actfac=2(IntACTime/.ac)/.IntACTime->1/2;
	If[optnegat,actfac=Max[1,actfac]];
	err=Sqrt[jackvar*actfac]*studfac;
	If[optverb,{ErrorBoundsRel[cent,err],Join[ret,ac]},ErrorBoundsRel[cent,err]]
	]

CookDownIndices[taken_,taketot_]:=Ceiling/@((Range[1,taken]-1/2)*(taketot/taken));
CookUpIndices[taken_,taketot_]:=Module[{ind,i,pos},
	ind=CookDownIndices[taken,taketot];
	ind=Append[Mean/@Partition[ind,2,1],taketot];
	pos=1;
	ind=Map[If[#>ind[[pos]],++pos,pos]&,Range[1,taketot]];
	ind=Split[ind];
	Flatten[Join[First/@ind,Rest/@ind]]
	]

ResamplingFit::ydatfmt="Second argument ydata must contain valid structures with resampled data.";
ResamplingFit::noautowt="Automatic weighting not possible for given ydata structure.";
ResamplingFit::baddat="Data samples with indeterminable errors."

ResamplingDataType[x_] := Which[
	MemberQ[x,JacknifeSamples,Infinity,Heads->True],JacknifeSamples,
	MemberQ[x,BootstrapSamples,Infinity,Heads->True],BootstrapSamples,
	True,None];

ResamplingFit[xdata_,ydata_,model_,modelvar_,modelpar_,opts___?OptionQ] := 
Module[{dt,n,ydata2,resid,res,res2,startparam,par,startval,der, jacob,doadjuststart,parspecs,weights,numsamples},
	{weights,doadjuststart,numsamples}={FitWeights,AdjustStartValues,NumSamples}/.Flatten[{opts,Options[JacknifeFit]}];
	
	dt=ResamplingDataType[ydata];
	If[dt===None,Message[ResamplingFit::ydatfmt];Abort[]];

	ydata2=StrucThread[dt,ydata];
	If[Head[ydata2]=!=dt,Message[JacknifeFit::ydatfmt];Abort[]];

	If[weights===1,weights=1&/@xdata];
	If[weights===Automatic,
		If[Dimensions[ydata2[[1]]]=!={Length[xdata]},Message[ResamplingFit::noautowt]; Abort[]];
		weights=dt@@#&/@Transpose[List@@ydata2];
		weights=CentralErrorBounds[ResamplingStatistics[#]][[2]]&/@weights;
		If[!RealQ[weights],Message[ResamplingFit::baddat]; Abort[]];
		weights=1/weights;
		];

	n=Length[ydata2]-1;
	If[numsamples=!=All,
		numsamples=Min[Max[2,numsamples],n];
		res=List@@ydata2[[CookDownIndices[numsamples,n]+1]];
		res2=ydata2[[1]]-Total[res[[CookUpIndices[numsamples,n]]]]/n; (* avoid artificial bias *)
		ydata2=dt@@Prepend[#+res2&/@res,ydata2[[1]]];
		];

	If[Length[Dimensions[modelpar]]==2,
		startval=modelpar[[All,2]]; par=modelpar[[All,1]],
		startval=0&/@modelpar; par=modelpar
		];

	der=D[model,#]&/@par;

	jacob[parval_List/;NumericQ[parval[[1]]]] := 
	Module[{sjac},
		sjac=der/.MapThread[Rule,{par,parval}];
		MapThread[(sjac/.MapThread[Rule,{modelvar,#1}])*#2 &,{xdata,weights}]
		];

	res2=Map[Function[{curydat},
		resid[parval_List/;NumericQ[parval[[1]]]] := 
		Module[{smod,fnval},
			smod=model/.MapThread[Rule,{par,parval}];
			fnval=Map[smod/.MapThread[Rule,{modelvar,#}] &,xdata];
			(fnval-curydat)*weights
			];
		parspecs=MapThread[List,{par,startval}];
		If[RealQ[curydat],
			res=FindMinimum[1/2resid[par].resid[par],parspecs, Method->{"LevenbergMarquardt", "Residual"->resid[par], "Jacobian"->jacob[par]}] ;
			If[doadjuststart,startval=res[[2,All,2]]; doadjuststart=False];
			{2 res[[1]],res[[2,All,2]]},
			{Indeterminate,Indeterminate&/@par}
			]
		],ydata2];

	If[numsamples=!=All,
		res2=res2[[Prepend[CookUpIndices[numsamples,n]+1,1]]]
		];
	res2
	];
JacknifeFit := ResamplingFit;

(* obsolete *)
JacknifePlot[jfitdat_JacknifeSamples,model_,modelvarrange_,modelpar_,plotopts_List,fillopts_List] := 
Module[{jfn,lower,upper,xprobe,pfn,plc,plf},
	jfn[xval_]:=JacknifeStatistics[Map[
		model/.{modelvarrange[[1]]->xval}/.MapThread[Rule,{modelpar,#[[2]]}]&,
		jfitdat
		],Autocorr->False,Verbose->False];
	lower={};
	upper={};
	xprobe={};
	pfn[xval_?NumericQ] := 
	Module[{v},
		v=jfn[xval];
		lower={lower,v[[1]]-v[[2]]};
		upper={upper,v[[1]]+v[[2]]};
		xprobe={xprobe,xval};
		v[[1]]
		];
	plc=Plot[pfn[modelvarrange[[1]]],modelvarrange,Evaluate[Sequence@@plotopts]];
	lower=Flatten[lower]; upper=Flatten[upper]; 
	xprobe=Flatten[xprobe];
	lower=Sort[MapThread[List,{xprobe,lower}]];
	upper=Sort[MapThread[List,{xprobe,upper}]];
	plf=ListLinePlot[{lower,upper},Filling->{1->{2}},Evaluate[Sequence@@fillopts]];
	Show[plf,plc]
	]

ResamplingPlot[jfitdat_,model_,modelvarrange_,modelpar_,plotopts_List,fillopts_List,OptionsPattern[]] := 
Module[{jfn,lower,upper,central,xprobe,pfn,plc,plf,erru,errl,pl},
	jfn[xval_]:=ResamplingStatistics[Map[
		model/.{modelvarrange[[1]]->xval}/.MapThread[Rule,{modelpar,#[[2]]}]&,
		jfitdat
		]];
	lower={};
	central={};
	upper={};
	xprobe={};
	pfn[xval_?NumericQ] := 
	Module[{v},
		v=jfn[xval];
		If[Head[v[[2]]]===List,{errl,erru}=v[[2]],errl=v[[1]]-v[[2]];erru=v[[1]]+v[[2]]];
		lower={lower,errl};
		central={central,v[[1]]};
		upper={upper,erru};
		xprobe={xprobe,xval};
		v[[1]]
		];
	plc=Plot[pfn[modelvarrange[[1]]],modelvarrange,Evaluate[Sequence@@plotopts]];
	lower=Flatten[lower]; central=Flatten[central]; upper=Flatten[upper]; 
	xprobe=Flatten[xprobe];
	central=Sort[MapThread[List,{xprobe,lower,central,upper}]];
	lower=Sort[MapThread[List,{xprobe,lower}]];
	upper=Sort[MapThread[List,{xprobe,upper}]];
	plf=ListLinePlot[{lower,upper},Filling->{1->{2}},Evaluate[Sequence@@fillopts]];
	pl=Show[plf,plc];
	If[OptionValue[GiveVertices],{pl,central},pl]
	]

(*Combine data from two statistically independent sources*)
(*Rescaling of fluctuations ensures that bias correction and error determination work appropriately for the combined set!*)
JacknifeCombine[samp1_JacknifeSamples,samp2_JacknifeSamples] := 
Module[{n1,n2,rescal1,rescal2},
	n1=Length[samp1]-1;
	n2=Length[samp2]-1;
	rescal1=Sqrt[(n1-1)/(n1 n2-1)] (List@@Rest[samp1]-samp1[[1]]) + samp1[[1]];
	rescal2=Sqrt[(n2-1)/(n1 n2-1)] (List@@Rest[samp2]-samp2[[1]]) + samp2[[1]];
	JacknifeSamples@@Prepend[Tuples[{rescal1,rescal2}],{samp1[[1]],samp2[[1]]}]
	]

Format[s_JacknifeSamples] := 
Module[{u,l},
	u=JacknifeStatistics[s,Verbose->False,Autocorr->False];
	l=Length[s]-1;
	u/.{ErrorBoundsRel[val_,err_]:>StringForm["\[LeftAngleBracket]``\!\(\*SubscriptBox[\"\[RightAngleBracket]\", \"``J\"]\)",ErrForm[ErrorBoundsRel[val,err]],l]}
	]


(********************************** Bootstrap Statistics *********************************)

BootstrapSamples/:Plus[a_BootstrapSamples,x__BootstrapSamples]:=BootstrapSamples@@MapThread[Plus,List@@#&/@{a,x}];
BootstrapSamples/:Times[a_BootstrapSamples,x__BootstrapSamples]:=BootstrapSamples@@MapThread[Times,List@@#&/@{a,x}];
BootstrapSamples/:x_BootstrapSamples*c_?NumericQ:=BootstrapSamples@@(List@@x*c);
BootstrapSamples/:x_BootstrapSamples^c_?NumericQ:=BootstrapSamples@@(List@@x^c);

Format[s_BootstrapSamples] := 
Module[{u,l,lv},
	u=BootstrapStatistics[s]//StdErrorBounds;
	l=Length[s];
	lv=l-Count[s,_?RealQ];
	If[lv>0,
		u/.{ErrorBoundsRel[val_,err_]:>StringForm["\[LeftAngleBracket]``\!\(\*SubscriptBox[\"\[RightAngleBracket]\", \"``-``B\"]\)",ErrForm[ErrorBoundsRel[val,err]],l-1,lv]},
		u/.{ErrorBoundsRel[val_,err_]:>StringForm["\[LeftAngleBracket]``\!\(\*SubscriptBox[\"\[RightAngleBracket]\", \"``B\"]\)",ErrForm[ErrorBoundsRel[val,err]],l-1]}
		]
	]


MakeBootstrapSampler::indivisible = "Number of configurations not divisible by blocksize ``.";

MakeBootstrapSamplerSellist[nsamples_,nconfigs_,blocksize_]:=Module[{sellist,effconf},
	If[Mod[nconfigs,blocksize]=!=0 || nconfigs<blocksize,
		Message[MakeBootstrapSampler::indivisible,blocksize]; Abort[]
		];
	effconf=nconfigs/blocksize;
	sellist=Partition[RandomInteger[{1,effconf},effconf*nsamples],effconf];
	If[blocksize>1,
		sellist=Map[Range[#*blocksize-blocksize+1,#*blocksize]&,sellist,{2}];
		sellist=Map[Flatten,sellist];
		];
	PrependTo[sellist,Range[1,nconfigs]];
	sellist
	];

MakeBootstrapSampler[nconfigs_,OptionsPattern[]] := 
Module[{estim,BootstrapSampler,sellist},
	estim=OptionValue[Estimator];
	sellist=MakeBootstrapSamplerSellist[OptionValue[NumSamples],nconfigs,OptionValue[BinSize]];
	BootstrapSampler[data_]:=BootstrapSamples@@Map[estim[data[[#]]]&,sellist];
	BootstrapSampler
	];

(* compatibility *)
MakeBootstrapSampler[nsamples_,nconfigs_,opts:OptionsPattern[]] := 
	MakeBootstrapSampler[nconfigs,Sequence@@FilterRules[{opts},Except[NumSamples]],NumSamples->nsamples];

CreateBootstrapSampler[nconfigs_,OptionsPattern[]] := 
Module[{estim,BootstrapSampler,sellist},
	Function[{data},BootstrapSamples@@Map[estim[data[[#]]]&,sellist]]/.{
		estim->OptionValue[Estimator],
		sellist->MakeBootstrapSamplerSellist[OptionValue[NumSamples],nconfigs,OptionValue[BinSize]]
		}	
	];



BootstrapStatistics[bootstrap_List,opts:OptionsPattern[]] :=
	Map[BootstrapStatistics[#,opts]&,bootstrap];
BootstrapStatistics[bootstrap_BootstrapSamples,opts:OptionsPattern[]] := 
Module[{bs,lo,up,sortl,cl,nbs},
	bs=StrucUnThread[BootstrapSamples,bootstrap];
	If[Head[bs]=!=BootstrapSamples,Return[BootstrapStatistics[bs,opts]]];
	cl=OptionValue[ConfidenceLevel];
	nbs=Length[bs]-1;
	bs=Select[Rest[bootstrap],RealQ];
	lo=Floor[Length[bs]*(1/2-cl/2)]+1;
	up=Floor[Length[bs]*(1/2+cl/2)]+1;
	sortl=Sort[List@@bs,#1<#2&];
	cl=First[bootstrap];
	If[!RealQ[cl] && Length[sortl]>=1,
		cl=If[OddQ[Length[sortl]],
			sortl[[(Length[sortl]+1)/2]],
			(sortl[[Length[sortl]/2]]+sortl[[Length[sortl]/2+1]])/2
			];
		];
	If[Length[bs]<Max[2,nbs/2],Return[ErrorBounds[cl,{Indeterminate,Indeterminate}]]];
	ErrorBounds[cl,sortl[[{lo,up}]]]
	];


ResamplingStatistics::nimp="``-Statistics not implemented";
ResamplingStatistics[dat_List,opts:OptionsPattern[]] :=
	Map[ResamplingStatistics[#,opts]&,dat];
ResamplingStatistics[dat_,opts:OptionsPattern[]] := 
Module[{defopt},
	defopt={Verbose->False,Autocorr->False};
	defopt=Join[{opts},FilterRules[defopt,Except[{opts}]]];
	Switch[Head[dat],
		JacknifeSamples,JacknifeStatistics[dat,Sequence@@FilterRules[defopt,Options[JacknifeStatistics]]],
		BootstrapSamples,BootstrapStatistics[dat,Sequence@@FilterRules[defopt,Options[BootstrapStatistics]]],
		_,Message[ResamplingStatistics::nimp,Head[dat]];Abort[]
		]
	];
	
WithSamples::norules="Expecting a substitution or a list of substitutions of the form <Symbol>-><Value/Samples>";
WithSamples::uneq="Not allowed to substitute different types or lengths of samples"; 
WithSamples[formula_,substitutions___]:=Module[{resampsubs,regularsubs,resamptype,dat,syms},
	regularsubs=Flatten[{substitutions}];
	(*lets save some time: get rid of all variables that don't appear in the formula *)
	regularsubs=Select[regularsubs,MemberQ[formula,#[[1]],{0,Infinity}]&];
	If[!And@@((Head[#]===Rule && Length[#]==2)&/@regularsubs),Message[WithSamples::norules]; Abort[]];
	resampsubs=Select[regularsubs,MemberQ[{BootstrapSamples,JacknifeSamples},Head[#[[2]]]]&];
	regularsubs=Complement[regularsubs,resampsubs];
	resamptype=Union[{Head[#],Length[#]}&/@resampsubs[[All,2]]];
	If[Length[resamptype]===0,Return[formula/.regularsubs]];
	If[Length[resamptype]>1,Message[WithSamples::uneq]; Abort[]];
	resamptype=resamptype[[1,1]];
	regularsubs=formula/.regularsubs;
	syms=resampsubs[[All,1]];
	resamptype@@Map[regularsubs/.MapThread[Rule,{syms,#}]&,Transpose[List@@#&/@resampsubs[[All,2]]]]
	];

End[];

EndPackage[];



