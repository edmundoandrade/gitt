BeginPackage["Calculus`GITT`","Calculus`CITT`","Algebra`Trigonometry`"]

ClearAll[GITT,eigenSolve,eigenValues];

GITT::usage =
"GITT[eqgov,eqicbc,unknown,nterms,t,{{x,xi,xf},...},flt,v,f,unknownt,opt]
transforms one partial differential equation (PDE) in a finite ordinary
differential equation (ODE) system by applying the Generalized Integral
Transform Technique (GITT) and gives a four-element list:
[[1]] the inversion formula for the specified unknown.
[[2]] the finite transformed ODE system with independent variable t.
[[3]] the initial conditions for the finite transformed ODE system.
[[4]] the transformed unknowns for the finite transformed ODE system.
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
The Calculus`CITT` and Algebra`Trigonometry` packages are used.";

(***********************************************************************)
Begin["`Private`"]
(***********************************************************************)

(***********************************************************************)
(*                    Solution of Parabolic PDE System                 *)
(***********************************************************************)

(*=========================== Main module =============================*)

GITT[eqgov_Equal,eqicbc_List,dv_,nt_,t_Symbol,{xyz__List},0,
	v_,f_,dvt_,opt___] :=
Module[{opgov,opicbc,varXYZ,ef,efn,w,tmp,cf,elim,h,
	eqauxgov,eqauxbc,svaux,rlinv,rltrf,rlgen,simp,
	exptrf,eqtrfgov,eqtrficbc,unknownsT},

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

  Print["Auxiliary Problem:"];
  Print[{eqauxgov,eqauxbc}];Print[""];

(* Obtain eigenvalues and eigenfunctions
   of the auxiliary problem *)

  svaux=eigenSolve[eqauxgov,eqauxbc,ef,v,nt,opt];
  If[svaux===$Failed,Return[$Failed]];

  Print["EigenValues:"];
  Print[svaux[[2]]];Print[""];

(* Express eigenfunctions in normalized form *)

  tmp=svaux[[1]] /. Times[C[_],expr_]->expr;
  tmp=Simplify[tmp / Sqrt[defIntegral[tmp^2,xyz]]];
  Do[efn[i][varXYZ]=Limit[tmp,v->svaux[[2,i]]],{i,nt}];

  Print["Normalized EigenFunction:"];
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

(* Simplify by using the boundary conditions *)

  exptrf=
    Select[eqtrfgov[[1]]-eqtrfgov[[2]],!FreeQ[#,Head[dv]]&];
  elim=Select[Union[
	Flatten[exptrf /. Thread[{Plus,Times}->List]]
	],!FreeQ[#,Head[dv]]&];
  simp=exptrf;
  Do[tmp=Solve[Flatten[{h[t]==simp,eqicbc,eqauxbc}],h[t],elim[[i]]];
     If[Length[tmp[[1]]]>0,simp=(h[t] /. tmp[[1]])];
  ,{i,Length[elim]}];
  eqtrfgov=(eqtrfgov[[1]]-eqtrfgov[[2]]-exptrf+simp==0);

(* Transform the initial or boundary conditions *)

  eqtrficbc={};
  Scan[(If[FreeQ[#,t],
    eqtrficbc={eqtrficbc,
	defIntegral[Thread[w ef #,Equal],xyz] /. rltrf}
    ])&
  ,eqicbc];
  eqtrficbc=Flatten[eqtrficbc];

  Print["Transformed ODE System:"];
  Print[eqtrfgov];Print[""];
  Print[eqtrficbc];Print[""];

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

(* Return inversion formula and transformed ODE *)

  {rlinv,Chop[eqtrfgov],Chop[eqtrficbc],unknownsT}

]

GITT[eqgov_Equal,eqicbc_List,dv_[vs__],nt_,t_Symbol,{xyz__List},flt_,
	v_,f_,dvt_,opt___] :=
Module[{eqgovh,eqicbch,dvh=SequenceForm[dv,"H"],ret},

(* Attach a filter function *)
  eqgovh=Chop[changeFunction[eqgov,dv[vs],flt+dvh[vs]] /.
	(a_==b_):>(Simplify[a-b]==0)];
  eqicbch=Chop[changeFunction[eqicbc,dv[vs],flt+dvh[vs]] /.
	(a_==b_):>(Simplify[a-b]==0)];

  Print["Homogeneous Problem:"];
  Print[{eqgovh,eqicbch}];Print[""];

  rlgen=Map[(#->Pattern[#,_])&,{vs}];
  ret=GITT[eqgovh,eqicbch,dvh[vs],nt,t,{xyz},0,v,f,dvt,opt];
  ret[[1]]=((dv[vs] /. rlgen) -> (flt+dvh[vs] /. ret[[1]]));
  ret

] /; flt=!=0

eigenSolve::cond = "eigencondition `1` couldn't be solved"

eigenSolve[eqgov_Equal,eqbc_List,f_[vs__],v_,n_,opt___] :=
Module[{glbsol,eigenc,fs,veqn,ret},
  fs=ComplexToTrig[DSolve[eqgov,f[vs],{vs}][[1]]//Chop];
  If[Head[fs]===DSolve,Return[$Failed]];
  glbsol=(f[vs] /. fs);
  eigenc=Map[changeFunction[#,f[vs],glbsol]&,eqbc];
  eigenc=Reduce[Append[eigenc,v!=0]];
  ret=$Failed;
  Scan[(fs=Simplify[glbsol /. ToRules[#]];
	If[fs=!=0,
	  veqn=Flatten[{# /. And->List}];
	  veqn=Select[veqn,(!FreeQ[#,v]&&Head[#]===Equal)&][[1]];
	  ret={fs,eigenValues[veqn[[1]]-veqn[[2]],v,n,0,0.1,opt]}
	])&
  ,Flatten[{eigenc /. Or->List}]];
  If[ret===$Failed,Message[eigenSolve::cond,eigenc]];
  ret
]

eigenValues[expr_,x_,n_Integer,base_,step_,opt___] :=
Module[{sol={},fst=base,lst,fx,sgn},
  fx=Compile[x,expr];
  Off[CompiledFunction::cfn,Power::infy];
  Do[	While[
	  While[lst=fst+step;(sgn=fx[fst] fx[lst])===ComplexInfinity,
	    fst=lst+step];
	  sgn>0,
	  fst=lst;lst=fst+step
	];
	sol={sol,x /. FindRoot[fx[x],{x,{fst,lst}},opt]};
	fst=lst
  ,{n}];
  On[CompiledFunction::cfn,Power::infy];
  Flatten[sol]
] /; Head[expr]=!=List && !NumberQ[x]

(***********************************************************************)
End[]		(* end `Private` Context                               *)
(***********************************************************************)

(***********************************************************************)
EndPackage[]	(* end package Context                                 *)
(***********************************************************************)









