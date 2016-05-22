(*:Context: Calculus`CITT` *)

(*:Title: Classical Integral Transform Technique *)

(*:Author: F.E. Andrade & J.W. Ribeiro *)

(*:Summary: This package implements Definite Integral for use with
Integral Transform Technique. Furthermore, it implements change of
functions, verification of linearity and extraction of operators
for any given differential expression.
*)

(*:Keywords: Function Change, Linearity, Operator, Definite Integral,
Integral transform
*)

BeginPackage["Calculus`CITT`"]

ClearAll[changeFunction,getOperator,isLinear,getLinearOperator,defIntegral];

changeFunction::usage =
"changeFunction[expr,f,g] gives expr after put the expression g
in place of the function f."

getOperator::usage =
"getOperator[expr,f] gives the operator of f in expr."

isLinear::usage =
"isLinear[expr,f] gives True if expr is linear with respect to f."

getLinearOperator::usage =
"getLinearOperator[expr,f] gives the linear operator of f in expr."

defIntegral::usage =
"defIntegral[expr,{x,xi,xf}] gives the definite integral of expr with
respect to x on domain [xi,xf]. It complements the built-in function
Integrate[ ] when classical integral transform technique (CITT) is used.
defIntegral[expr,{x,xi,xf},{y,yi,yf},...] gives a multiple integral."

(***********************************************************************)
Begin["`Private`"]
(***********************************************************************)

Clear[dPartial];

(***********************************************************************)
(*          Function change on a given expression or equation          *)
(***********************************************************************)

changeFunction[expr_,f_Symbol,g_] :=
  expr /. f->g

changeFunction[expr_,f_[vs___Symbol],g_] :=
  expr /; FreeQ[expr,f]

changeFunction[f_[vi___],f_[vs___Symbol],g_] :=
  Module[{subst={}},
	Scan[(If[{vs}[[#]]=!={vi}[[#]],
	  subst={subst,{vs}[[#]]->{vi}[[#]]}])&
	,Range[Length[{vi}]]];
	subst=Flatten[subst];
	If[Head[g]===Hold && Length[subst]>0,
	  Function[{a,b},Hold[a /. b]][g,subst],
	  g /. subst]
  ] /; Length[{vi}]==Length[{vs}]

changeFunction[Derivative[ni___][f_][vi___],f_[vs___Symbol],g_] :=
  Module[{dv={g},subst={}},
	Scan[(AppendTo[dv,{{vs}[[#]],{ni}[[#]]}];
	  If[{vs}[[#]]=!={vi}[[#]],
	  subst={subst,{vs}[[#]]->{vi}[[#]]}])&
	,Range[Length[{vi}]]];
	subst=Flatten[subst];
	If[Head[g]===Hold && Length[subst]>0,
	  Function[{a,b},Hold[a /. b]][Apply[D,dv],subst],
	  Apply[D,dv] /. subst]
  ] /; Length[{vi}]==Length[{vs}]

changeFunction[h_[a___],f_[vs___Symbol],g_] :=
  Apply[h,Map[changeFunction[#,f[vs],g]&,{a}]]

(***********************************************************************)
(*             Operator extraction from a given expression             *)
(***********************************************************************)

getOperator[expr_,f_Symbol] :=
  Evaluate[Select[expr+1+Pi,!FreeQ[#,f]&] /. f->#]&

getOperator[expr_,f_[vs___Symbol]] :=
  Module[{fdep,g},
	fdep=Select[expr+1+Pi,!FreeQ[#,f]&];
	(Evaluate[changeFunction[fdep,f[vs],Hold[g]]])& //.
	{Hold[g]->#,Hold[r_ReplaceAll]->r}
  ]

(***********************************************************************)
(*            Linearity verification for a given expression            *)
(***********************************************************************)

isLinear[expr_,f_Symbol] :=
  Module[{op,u,v},
	op=getOperator[expr,f];
	Simplify[op[u+v]-op[u]-op[v]]===0
  ]

isLinear[expr_,f_[vs___Symbol]] :=
  Module[{op,u,v},
	op=getOperator[expr,f[vs]];
	Simplify[op[u[vs]+v[vs]]-op[u[vs]]-op[v[vs]]]===0
  ]

(***********************************************************************)
(*         Linear Operator extraction from a given expression          *)
(***********************************************************************)

getLinearOperator[expr_,f_] :=
  Module[{linexp=0},
	Scan[If[isLinear[#,f],linexp=linexp+#]&
	,Expand[expr+1+Pi]];
	getOperator[linexp,f]
  ]

(***********************************************************************)
(*                    Definite Integral extension                      *)
(***********************************************************************)

(*=========================== Linearity ===============================*)

defIntegral[c_, {x_Symbol,xi_,xf_}] :=
	c (xf - xi) /; FreeQ[c,x]

defIntegral[c_ f_, s:{x_Symbol,_,_}] :=
	Expand[c defIntegral[f, s]] /; FreeQ[c,x]

defIntegral[o_Plus, s_] :=
	defIntegral[#, s]& /@ o

defIntegral[f_. Sum[g_, {n_,ni_,nf_}], s:{x_Symbol,_,_}] :=
	Sum[defIntegral[f g, s],{n,ni,nf}] /;
	FreeQ[{n,ni,nf},x] && FreeQ[f,n]

defIntegral[f_, s_] :=
  Module[{ff = TrigExpand[f]},
	defIntegral[ff, s] /; ff=!=f
  ] /; Head[f]===Times || Head[f]===Power

defIntegral[o_Equal, s_] :=
	(defIntegral[#, s]& /@ o) /. (c_+f_==c_+g_ -> f==g)

(*=============== defIntegral, Listable on First arg only =============*)

defIntegral[expr_List, args___] := Map[ defIntegral[#,args]&,expr ]

(*================ defIntegral, Multidimensional form  ================*)

defIntegral[expr_,s:{_Symbol,_,_},ss___List] :=
	defIntegral[defIntegral[expr,ss],s] /; Length[{ss}]>0

(*============= defIntegral, Composition with Derivative ==============*)

defIntegral[f_. Derivative[nd___][g_][vg___], s:{x_Symbol,_,_}] :=
  Module[{v,ndv,nnd={nd}},
	dPartial[defIntegral[f Apply[Derivative,nnd][g][vg], s],{v,ndv}] /;
	Scan[(v = {vg}[[#]];
		If[nnd[[#]] > 0 && FreeQ[f,v] && FreeQ[v,x],
			ndv = nnd[[#]];nnd[[#]] = 0;Return[True]]
		)&,Range[Length[{vg}]]]
  ]

(*========= Built-in funcionality of the Indefinite Integrate =========*)

defIntegral[f_, s:{x_Symbol,xi_,xf_}] :=
  Module[{it=Integrate[f,x],is,iv},
	(is = Select[1+it,FreeQ[#,Integrate]&];
	iv = Select[1+it,!FreeQ[#,Integrate]&] /.
	Integrate[g_,x]:>defIntegral[g,s];
	(is/.x->xf)-(is/.x->xi)+iv ) /;
	Head[it]=!=Integrate
  ]

(***********************************************************************)
(*                     Partial Derivative extension                    *)
(***********************************************************************)

dPartial[f_,{x_,nd_}] := D[f,{x,nd}] /;
	FreeQ[f,defIntegral]

(***********************************************************************)
End[]		(* end `Private` Context                               *)
(***********************************************************************)

(***********************************************************************)
EndPackage[]	(* end package Context                                 *)
(***********************************************************************)
