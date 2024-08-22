(* ::Package:: *)

(* BCJNumeratorsMod.m 
   modified by Tara Leininger for use as package*)

(* BCJ_Numerators.m 
   from "Covariant Color-Kinematics Duality" 
   by Clifford Cheung and James Mangan *)
   
(* This supplemental file computes BCJ numerators for YM theory for
   arbitrary numbers of external legs in general spacetime dimension.
   
   The variables pp[i,j], pe[i,j], and ee[i,j] are the usual kinematic
   invariants built from momenta and polarizations.  Leg 0 labels a
   universal reference momentum vector. 
   
   The function K0[n] outputs a symbolic expression for the n-point BCJ
   numerator in terms of the field strength trace F0 and kinematic
   function G0.  The function K[n] is the same expression in terms of 
   explicit kinematic invariants. *)


(* Kinematics *)

(*BeginPackage["myPackage`"]
myPublicFunction::usage="myPublicFunction blahblahblah";
Begin["Private"]
myPrivateFunction[input_]:= ... ;
myPublicFunction[input_]:= ... ;
End[]
EndPackage[]*)
BeginPackage["BCJNumeratorsMod`"]

K::usage="K[n] gives BCJ numerator at n point";


SetAttributes[pp,Orderless];
SetAttributes[ee,Orderless];
ToInvariants[x_]:=Expand[x]//.{
p[i_][a_]p[j_][a_]:>pp[i,j],
e[i_][a_]e[j_][a_]:>ee[i,j],
p[i_][a_]e[j_][a_]:>pe[i,j]};
Momentum[\[Sigma]__][a_]:=Total[Map[p[#][a]&,{\[Sigma]}]];
FieldStrength[i_][a_,b_]:=p[i][a]e[i][b]-p[i][b]e[i][a];
FieldStrength[\[Sigma]__,i_][a_,b_]:=Module[{c},FieldStrength[\[Sigma]][a,c]FieldStrength[i][c,b]]//ToInvariants;
FieldStrengthTilde[i_][a_,b_]:=1/pp[0,i] (p[0][a]e[i][b]-p[0][b]e[i][a]);


(* F and G *)
Begin["`Private`"]
F[\[Sigma]__,n_]:=Module[{a,b},1/2 FieldStrength[\[Sigma]][a,b]FieldStrengthTilde[n][b,a]]//ToInvariants;
G[\[Sigma]__][\[Tau]__][\[Rho]__,n_]:=Module[{a,b,c},-((Momentum[\[Sigma]][a]FieldStrength[\[Tau]][a,b]p[0][b]//ToInvariants)/(Momentum[\[Sigma],\[Rho],n][c]p[0][c]//ToInvariants))];
G[\[Sigma]__][\[Tau]__][n_]:=Module[{a,b,c},-((Momentum[\[Sigma]][a]FieldStrength[\[Tau]][a,b]p[0][b]//ToInvariants)/(Momentum[\[Sigma],n][c]p[0][c]//ToInvariants))];


(* BCJ Numerators *)

Needs["Combinatorica`"];
part[x_]:=Select[Flatten[Permutations/@SetPartitions[Range[x]],1],MemberQ[#[[1]],1]&];
K0[n_]:=Sum[F0[\[Tau][[1]]~Join~{n}]Times@@(Table[G0[Select[Flatten[\[Tau][[1;;i-1]]],#<Min[\[Tau][[i]]]&],\[Tau][[i]],Select[Flatten[\[Tau][[1;;i-1]]],#>Min[\[Tau][[i]]]&]~Join~{n}],{i,2,Length[\[Tau]]}]),{\[Tau],part[n-1]}]/.{F0[{x__}]:>F0[x],G0[{x__},{y__},{z__}]:>G0[x][y][z]};
K[n_]:=K0[n]/.{F0->F,G0->G};
End[]
EndPackage[]
