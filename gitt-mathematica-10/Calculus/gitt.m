(* ::Package:: *)

BeginPackage["Calculus`GITT`","Calculus`CITT`"]

ClearAll[GITT,eigenSolve,eigenValues];

GITT::usage =
"GITT[eqgov,eqicbc,unknown,nterms,t,{{x,xi,xf},...},flt,v,f,unknownt,opt]
transforms one partial differential equation (PDE) in a finite ordinary
differential equation (ODE) system by applying the Generalized Integral
Transform Technique (GITT) and gives the resulting solution.
The argument eqgov is the PDE to be transformed.
The argument eqicbc is a list containing initial and boundary conditions.
The argument unknown is the unknown variable.
The argument nterms is the truncation order number.
The argument t is the independent variable for the transformed ODE.
The argument x is an independent variable to be transformed.
The arguments xi,xf are the limits of domain of x.
The argument flt is a filter function that satisfies boundary conditions.
The argument v is any symbol to identify the eigenvalues.
The argument f is any symbol to identify the eigenfunctions.
The argument unknownt is any symbol to identify the transformed unknown.
The argument opt is used to define options like WorkingPrecision->d.
The Calculus`CITT` package is required.";

(***********************************************************************)
Begin["`Private`"]
(***********************************************************************)

(***********************************************************************)
(*                    Solution of Parabolic PDE System                 *)
(***********************************************************************)

(*=========================== Main module =============================*)

GITT[eqgov_Equal,eqicbc_List,dv_,nt_,t_Symbol,{xyz__List},0,
	v_,f_,dvt_,opt___] :=
Module[{opgov,opicbc,varXYZ,ef,efn,w,tmp,cf,h,
	eqauxgov,eqauxbc,svaux,rlef,rlinv,rltrf,rlgen,simp,
	exptrf,eqtrfgov,eqtrficbc,unknownsT,edosol,anasol},

(* Independent variables to eliminate *)

  varXYZ={};
  Scan[(varXYZ={varXYZ,#[[1]]})&,{xyz}];
  varXYZ=Apply[Sequence,Flatten[varXYZ]];

(* Extract linear operators of the PDE *)

  opgov=getLinearOperator[eqgov[[1]]-eqgov[[2]],dv];
  opicbc={};
  Scan[(If[!FreeQ[#,t],
    opicbc={opicbc,getLinearOperator[#[[1]]-#[[2]],dv]}])&
  ,eqicbc];
  opicbc=Flatten[opicbc];

(* Compose auxiliary problem using extracted operators *)

  ef=f[varXYZ];
  w=Last[Flatten[ {opgov[dvt[t]] /.
	{Plus->List,Derivative[_][dvt][t]->1}} ]];
  eqauxgov=(opgov[ef]==w v^2 ef);
  eqauxbc=Map[(#[ef]==0)&,opicbc];

  Print["Auxiliary problem:"];
  Print[{eqauxgov,eqauxbc}];

(* Obtain eigenvalues and eigenfunctions
   of the auxiliary problem *)

  svaux=eigenSolve[eqauxgov,eqauxbc,ef,v,nt,opt];
  If[svaux===$Failed,Return[$Failed]];

  Print[""];
  Print[Row[{"EigenValues ", v, ":"}]];
  Print[svaux[[2]]];Print[""];

(* Express eigenfunctions in normalized form *)

  tmp=svaux[[1]] /. Times[C[_],expr_]->expr;
  tmp=Simplify[tmp / Sqrt[defIntegral[tmp^2,xyz]]];
  rlef=ef->tmp;
  Do[efn[i][varXYZ]=Limit[tmp,v->svaux[[2,i]]],{i,nt}];

  Print[Row[{"Normalized eigenFunctions ", ef, ":"}]];
  Print[rlef];
  Print[Table[efn[i][varXYZ],{i,nt}]];Print[""];

(* Develop the Integral Transform Pair considering
   the ortogonality of the eigenfunctions *)

  rlgen=Map[(#->Pattern[#,_])&,{varXYZ,t}];
  tmp=(defIntegral[w ef dv,xyz]);
  cf=(tmp /. defIntegral[__]->1);
  rltrf=((tmp/cf /. rlgen) -> dvt[t]/cf);
  rlinv=((dv /. rlgen) -> Sum[dvt[i][t] efn[i][varXYZ],{i,nt}]);

(* Apply Method of Solution to transform the PDE in ODE *)

  eqtrfgov=
    (defIntegral[ef (eqgov[[1]]-eqgov[[2]])
		-dv (eqauxgov[[1]]-eqauxgov[[2]])
    ,xyz] == 0) /. rltrf;
  (* If possible, apply Green's theorem *)
  eqtrfgov=eqtrfgov /.
    defIntegral[a_,vars_]-defIntegral[b_,vars_]:>defIntegralFromIndefinite[a-b,vars];
  eqtrfgov=eqtrfgov /.
    defIntegralFromIndefinite:>defIntegral;

(* Simplify by using the boundary conditions *)

  exptrf=
    Select[eqtrfgov[[1]]-eqtrfgov[[2]],!FreeQ[#,Head[dv]]&];
  simp=Simplify[exptrf,Flatten[{eqicbc,eqauxbc}]];
  eqtrfgov=(eqtrfgov[[1]]-eqtrfgov[[2]]-exptrf+simp==0);

(* Transform the initial or boundary conditions *)

  eqtrficbc={};
  Scan[(If[FreeQ[#,t],
    eqtrficbc=Append[eqtrficbc, defIntegral[Thread[w ef #,Equal],xyz] /. rltrf]
    ])&
  ,eqicbc];

  Print["Transformed ODE system:"];
  Print[eqtrfgov];
  Print[eqtrficbc /. {rlef,defIntegral:>Integrate}];

(* Assemble the ODE system based in the eigenvalues truncated list *)

  eqtrfgov=Table[
	changeFunction[eqtrfgov,ef,efn[i][varXYZ]] /.
	{dvt->dvt[i],v->svaux[[2,i]]}
	,{i,nt}];
  eqtrficbc=Flatten[Table[
	changeFunction[eqtrficbc,ef,efn[i][varXYZ]] /.
	{dvt->dvt[i],v->svaux[[2,i]]}
	,{i,nt}]];
  unknownsT=Table[dvt[i][t],{i,nt}];

(* Apply the inversion formula on the untrasformed terms *)

  eqtrfgov=(eqtrfgov /. rlinv);

(* Solve ODE system *)

  edosol=First[DSolve[Join[eqtrfgov,eqtrficbc],unknownsT,t]];
  Print[edosol /. dvt[i_]->Subscript[dvt,i]];Print[""];

(* Return solution *)

  Print["Inversion formula"];
  Print[rlinv /. dvt[i_]->Subscript[dvt,i]];Print[""];
  anasol=Expand[rlinv /. edosol];
  Print["Analytic solution"];
  Print[anasol];
  anasol
]

GITT[eqgov_Equal,eqicbc_List,dv_[vs__],nt_,t_Symbol,{xyz__List},flt_,
	v_,f_,dvt_,opt___] :=
Module[{eqgovh,eqicbch,dvh=SequenceForm[dv,"H "],ret},

(* Attach a filter function *)
  eqgovh=changeFunction[eqgov,dv[vs],flt+dvh[vs]] /.
	(a_==b_):>(Simplify[a-b]==0);
  eqicbch=changeFunction[eqicbc,dv[vs],flt+dvh[vs]] /.
	(a_==b_):>(Simplify[a-b]==0);

  Print["Homogeneous problem:"];
  Print[{eqgovh,eqicbch}];Print[""];

  rlgen=Map[(#->Pattern[#,_])&,{vs}];
  ret=GITT[eqgovh,eqicbch,dvh[vs],nt,t,{xyz},0,v,f,dvt,opt];
  anasol=Expand[(dv[vs] /. rlgen) -> (flt+dvh[vs] /. ret)];
  Print[anasol];
  anasol
] /; flt=!=0

eigenSolve::cond = "eigencondition `1` couldn't be solved "

eigenSolve[eqgov_Equal,eqbc_List,f_[vs__],v_,n_,opt___] :=
Module[{glbsol,eigenc,eigensol,fs,veqn,ret,vsi},
  If[Length[{vs}]===1,vsi=vs,vsi={vs}];
  fs=ExpToTrig[DSolve[eqgov,f[vs],vsi][[1]]];
  If[Head[fs]===DSolve,Return[$Failed]];
  glbsol=(f[vs] /. fs);
  eigenc=Map[changeFunction[#,f[vs],glbsol]&,eqbc];
  eigenc={Simplify[Eliminate[eigenc,C[1]],\[Mu]!=0],Simplify[Eliminate[eigenc,C[2]],\[Mu]!=0]};
  eigenc=eigenc /. (v C[i_]==0 -> C[i]==0);
  Off[Reduce::nsmet];
  eigensol=Reduce[Join[eigenc,{v!=0,C[1]!=0||C[2]!=0}],{C[1],C[2]}];
  On[Reduce::nsmet];
  If[Head[eigensol]=!=Reduce, eigenc=eigensol];
  eigenc=eigenc /. (x_==2 \[Pi] C[i_]||x_==\[Pi]+2 \[Pi] C[i_])->x==\[Pi] C[i];
  eigenc=eigenc /. (x_==-\[Pi]/2+2 \[Pi] C[i_]||x_==\[Pi]/2+2 \[Pi] C[i_])->x==\[Pi]/2+\[Pi] C[i];
  Print[Subscript[f,v][vs]==glbsol];
  Print[eigenc];
  fs=Simplify[glbsol, eigenc];
  ret=$Failed;
  Scan[(
	If[fs=!=0,
	  veqn=Flatten[{# /. And->List}];
	  veqn=Select[veqn,(!FreeQ[#,v]&&Head[#]===Equal)&];
	  If[Length[veqn] > 0,
		veqn=veqn[[1]];
		If[veqn[[1]]===v && FreeQ[veqn[[2]],v],
		  ret={fs,eigenValues[v,n,veqn[[2]],Cases[veqn[[2]],C[i_],Infinity][[1]],fs,vs]},
		  ret={fs,eigenValues[veqn[[1]]-veqn[[2]],v,n,0.1,0.1,opt]}
		]
	  ];
	])&,
    Flatten[{eigenc /. Or->List}]
  ];
  If[ret===$Failed,Message[eigenSolve::cond,eigenc]];
  ret
]

eigenValues[x_,n_Integer,expr_,var_,fs_,vs_] :=
Module[{sol={},k,value,trials},
  k=0;
  trials=0;
  While[Length[sol]<n && trials<n*2,
    trials++;
	value=expr /. var->k;
	If[!FreeQ[fs /. x->value,vs], sol=Append[sol, value]];
	k++
  ];
  sol
] /; Head[expr]=!=List && !NumberQ[x]

eigenValues[expr_,x_,n_Integer,base_,step_,opt___] :=
Module[{sol={},fst=base,lst,fx,sgn},
  fx=Compile[x,expr /. C[_]->1];
  Off[CompiledFunction::cfn,CompiledFunction::cfsa,Power::infy];
  Do[
	While[
	  While[lst=fst+step;(sgn=fx[fst] fx[lst])===ComplexInfinity,
	    fst=lst+step];
	  sgn>0,
	  fst=lst;lst=fst+step
	];
	sol=Append[sol,x /. FindRoot[fx[x],{x,{fst,lst}},opt] /. {v1_,v2_}->v1];
	fst=lst
    ,{n}
  ];
  On[CompiledFunction::cfn,CompiledFunction::cfsa,Power::infy];
  sol
] /; Head[expr]=!=List && !NumberQ[x] && NumberQ[step]

(***********************************************************************)
End[]		(* end `Private` Context                               *)
(***********************************************************************)

(***********************************************************************)
EndPackage[]	(* end package Context                                 *)
(***********************************************************************)












