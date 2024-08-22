(* ::Package:: *)

(*Inverse KLT Matrix Entries for 4,5,6 point*)
S[{2},{2}]=1/(\!\(\*SubscriptBox[\(s\), \({1, 2}\)]\));
{{S[{2,3},{2,3}],S[{3,2},{2,3}]},{S[{2,3},{3,2}],S[{3,2},{3,2}]}}=1/(\!\(\*SubscriptBox[\(s\), \({1, 2, 3}\)]\)){{1/(\!\(\*SubscriptBox[\(s\), \({1, 2}\)]\))+1/(\!\(\*SubscriptBox[\(s\), \({2, 3}\)]\)),-1/(\!\(\*SubscriptBox[\(s\), \({2, 3}\)]\))},{-1/(\!\(\*SubscriptBox[\(s\), \({2, 3}\)]\)),1/(\!\(\*SubscriptBox[\(s\), \({1, 3}\)]\))+1/(\!\(\*SubscriptBox[\(s\), \({2, 3}\)]\))}};
S[{b_,c_,d_},{b_,c_,d_}]=1/(\!\(\*SubscriptBox[\(s\), \({1, b, c, d}\)]\))(1/(\!\(\*SubscriptBox[\(s\), \({b, c, d}\)]\))(1/(\!\(\*SubscriptBox[\(s\), \({b, c}\)]\))+1/(\!\(\*SubscriptBox[\(s\), \({c, d}\)]\)))+1/(\!\(\*SubscriptBox[\(s\), \({1, b}\)]\)*\!\(\*SubscriptBox[\(s\), \({c, d}\)]\))+1/(\!\(\*SubscriptBox[\(s\), \({1, b, c}\)]\))(1/(\!\(\*SubscriptBox[\(s\), \({1, b}\)]\))+1/(\!\(\*SubscriptBox[\(s\), \({b, c}\)]\))));
S[{b_,d_,c_},{b_,c_,d_}]=-1/(\!\(\*SubscriptBox[\(s\), \({1, b, c, d}\)]\)*\!\(\*SubscriptBox[\(s\), \({c, d}\)]\))(1/(\!\(\*SubscriptBox[\(s\), \({1, b}\)]\))+1/(\!\(\*SubscriptBox[\(s\), \({b, c, d}\)]\)));
S[{c_,b_,d_},{b_,c_,d_}]=-1/(\!\(\*SubscriptBox[\(s\), \({1, b, c, d}\)]\)*\!\(\*SubscriptBox[\(s\), \({b, c}\)]\))(1/(\!\(\*SubscriptBox[\(s\), \({1, b, c}\)]\))+1/(\!\(\*SubscriptBox[\(s\), \({b, c, d}\)]\)));
S[{d_,c_,b_},{b_,c_,d_}]=1/(\!\(\*SubscriptBox[\(s\), \({1, b, c, d}\)]\)*\!\(\*SubscriptBox[\(s\), \({b, c, d}\)]\))(1/(\!\(\*SubscriptBox[\(s\), \({b, c}\)]\))+1/(\!\(\*SubscriptBox[\(s\), \({c, d}\)]\)));
S[{c_,d_,b_},{b_,c_,d_}]=-1/(\!\(\*SubscriptBox[\(s\), \({1, b, c, d}\)]\)*\!\(\*SubscriptBox[\(s\), \({c, d}\)]\)*\!\(\*SubscriptBox[\(s\), \({b, c, d}\)]\));
S[{d_,b_,c_},{b_,c_,d_}]=-1/(\!\(\*SubscriptBox[\(s\), \({1, b, c, d}\)]\)*\!\(\*SubscriptBox[\(s\), \({b, c}\)]\)*\!\(\*SubscriptBox[\(s\), \({b, c, d}\)]\));


(*Generate BCJ relations*)
posn[set_,num_]:=Module[{pos},
pos=Flatten[Position[set, num]];
Which[Length[pos]== 1,pos[[1]],Length[pos]==0,0, Length[pos]>1,"error"]]


(*ordered and partially ordered permuations*)
OP[listA_List,listB_List]:=(*from ChatGPT*)
Module[{n=Length[listA],m=Length[listB],indices,insertPositions,allInsertions},indices=Tuples[{0,1},n+m];
indices=Select[indices,Total[#]==m&];
insertPositions=Flatten@Position[#,1]&/@indices;
allInsertions=Map[Function[positions,Module[{aIndex=1,bIndex=1},Table[If[MemberQ[positions,i],listB[[bIndex++]],listA[[aIndex++]]],{i,1,n+m}]]],insertPositions];
allInsertions]

POP[listA_,listB_]:=Module[{lengthA,permA},
lengthA=Length[listA];
permA=Permutations[listA,{lengthA}];
Flatten[Map[OP[#,listB]&,permA],1]]


(*functions for building BCJ relations*)
t[set_,n_,m_]:=Module[{pos3, pos},
pos = posn[set,n];
Which[n==m+1,0,n==3,t[set,5,m], n==n,pos ]]

G[i_,j_]:=Which[j==1,Subscript[s, Sort[{i,j}]], j==3,Subscript[s, Sort[{i,j}]], i<j,Subscript[s, Sort[{i,j}]],i==i,0]

F[\[Rho]_,k_,m_]:=Module[{n,tk,tkminus,tkplus,gsum,mands},
n=Length[\[Rho]]+1;
tk=t[\[Rho],k,m];
tkminus=t[\[Rho],k-1,m];
tkplus=t[\[Rho],k+1,m];
gsum=Which[tkminus<tk,Sum[G[k,\[Rho][[\[ScriptL]]]],{\[ScriptL],tk,n-1}],tkminus>tk,-Sum[G[k,\[Rho][[\[ScriptL]]]],{\[ScriptL],1,tk}]];
mands=Which[tkminus<tk<tkplus,Subscript[s, Sort[Join[{2},Range[4,k]]]],tkminus>tk>tkplus,-Subscript[s, Sort[Join[{2},Range[4,k]]]],tk==tk,0];
gsum+mands
]

BCJ\[Alpha]\[Beta]0[set_]:=(*for KK basis starting with 1,2 fixed and 3 fixed in BCJ*)
Module[{n,nminus,pos1,pos3,\[Alpha],\[Beta],\[Gamma]},
n=Length[set];
pos3=Flatten[ Position[set,3]];
\[Alpha]=Take[set,{3,pos3[[1]]-1}];
\[Beta]=Which[n>pos3[[1]],Take[set,{pos3[[1]]+1,n}],pos3[[1]]==n,{}];
\[Gamma]={\[Alpha],\[Beta]};
Return[\[Gamma]]
]

KKtoBCJ0[\[Sigma]_]:=(*for KK basis starting with 1,2 fixed and 3 fixed in BCJ*)
Module[{n,pops,\[Gamma],m},
n=Length[\[Sigma]];
\[Gamma]=BCJ\[Alpha]\[Beta]0[\[Sigma]];
pops=POP[\[Gamma][[1]],\[Gamma][[2]]];
m=Which[Length[\[Gamma][[1]]]==0,0,Length[\[Gamma][[1]]]==Length[\[Gamma][[1]]],Last[\[Gamma][[1]]]];
Total[Map[A[Join[{1,2,3},#]]*Product[F[Join[{3},#,{1}],k,m]/Subscript[s, Sort[Join[{2},Range[4,k]]]],{k,4,m}]&, pops]]
]


(*functions for rewriting BCJ relations*)
ChangeBasis[expr_,n_]:=(*for KK basis ending in n-1,n fixed and 1 fixed in BCJ*)
Module[{listOld,tlist,tmp,listNew,alist,rules1,rules2},
alist=Take[ToExpression[CharacterRange["a","z"]],n-3];
listOld=Range[n];
tlist=Array[tmp[#]&,n];
listNew=Join[{n-1,n,1},alist];
rules1=MapThread[Rule,{listOld,tlist}];
rules2=MapThread[Rule,{tlist,listNew}];
expr/.rules1/.rules2
]

ChangeBasisR[expr_,n_]:=(*for KK basis ending in n,n-1 fixed and 1 fixed in BCJ*)
Module[{listOld,tlist,tmp,listNew,alist,rules1,rules2},
alist=Take[ToExpression[CharacterRange["a","z"]],n-3];
listOld=Range[n];
tlist=Array[tmp[#]&,n];
listNew=Join[{n,n-1,1},alist];
rules1=MapThread[Rule,{listOld,tlist}];
rules2=MapThread[Rule,{tlist,listNew}];
expr/.rules1/.rules2
]

CycA[expr_,n_]:= (*rotates argument of A[] for rewriting formulas*)
expr/.A[\[Alpha]_]:>A[Permute[\[Alpha],CyclicGroup[n]][[3]]]


(*write BCJ equations to file*)
WriteBCJS[]:=Module[{},
BCJ=OpenWrite["BCJ_formulas"];
Write[BCJ,CycA[ChangeBasis[KKtoBCJ0[{1,2,4,3}],4],4]];
Write[BCJ,CycA[ChangeBasis[KKtoBCJ0[{1,2,3,4}],4],4]];

Write[BCJ,CycA[ChangeBasis[KKtoBCJ0[{1,2,4,5,3}],5],5]];
Write[BCJ,CycA[ChangeBasis[KKtoBCJ0[{1,2,4,3,5}],5],5]];
Write[BCJ,CycA[ChangeBasis[KKtoBCJ0[{1,2,3,4,5}],5],5]];

Write[BCJ,CycA[ChangeBasis[KKtoBCJ0[{1,2,4,5,6,3}],6],6]];
Write[BCJ,CycA[ChangeBasis[KKtoBCJ0[{1,2,4,5,3,6}],6],6]];
Write[BCJ,CycA[ChangeBasis[KKtoBCJ0[{1,2,4,3,5,6}],6],6]];
Write[BCJ,CycA[ChangeBasis[KKtoBCJ0[{1,2,3,4,5,6}],6],6]];
Close[BCJ];

BCJR=OpenWrite["BCJR_formulas"];
Write[BCJR,CycA[ChangeBasisR[KKtoBCJ0[{1,2,4,3}],4],4]];
Write[BCJR,CycA[ChangeBasisR[KKtoBCJ0[{1,2,3,4}],4],4]];

Write[BCJR,CycA[ChangeBasisR[KKtoBCJ0[{1,2,4,5,3}],5],5]];
Write[BCJR,CycA[ChangeBasisR[KKtoBCJ0[{1,2,4,3,5}],5],5]];
Write[BCJR,CycA[ChangeBasisR[KKtoBCJ0[{1,2,3,4,5}],5],5]];

Write[BCJR,CycA[ChangeBasisR[KKtoBCJ0[{1,2,4,5,6,3}],6],6]];
Write[BCJR,CycA[ChangeBasisR[KKtoBCJ0[{1,2,4,5,3,6}],6],6]];
Write[BCJR,CycA[ChangeBasisR[KKtoBCJ0[{1,2,4,3,5,6}],6],6]];
Write[BCJR,CycA[ChangeBasisR[KKtoBCJ0[{1,2,3,4,5,6}],6],6]];
Close[BCJR];
]


(*functions for changing basis for color ordered amplitudes*)

CycOrdering[set_]:=(*for KK basis ending in n-1,n fixed and 1 fixed in BCJ*)
Module[{n,cycles},
n=Length[set];
cycles=SortBy[Permute[set,CyclicGroup[n]],Last];
cycles[[n]]
]

KK\[Alpha]\[Beta][set_]:=(*for KK basis ending in n-1,n fixed and 1 fixed in BCJ*)
Module[{n,nminus,posn,posnminus,\[Alpha],\[Beta],\[Gamma],set1},
set1=CycOrdering[set];
n=Length[set];
nminus=n-1;
posn=Flatten[ Position[set1,n]];
posnminus=Flatten[ Position[set1,nminus]];
\[Alpha]=Take[set1,posnminus[[1]]-1];
\[Beta]=Which[posn[[1]]>posnminus[[1]]+1,Take[set1,{posnminus[[1]]+1,posn[[1]]-1}],posn[[1]]==posnminus[[1]]+1,{}];
\[Gamma]={\[Alpha],\[Beta]};
Return[\[Gamma]]
]

BCJ\[Alpha]\[Beta][set_]:=(*for KK basis ending in n-1,n fixed and 1 fixed in BCJ*)
Module[{n,nminus,pos1,posnminus,\[Alpha],\[Beta],\[Gamma]},
n=Length[set];
nminus=n-1;
pos1=Flatten[ Position[set,1]];
posnminus=Flatten[ Position[set,nminus]];
\[Alpha]=Take[set,pos1[[1]]-1];
\[Beta]=Which[posnminus[[1]]>pos1[[1]]+1,Take[set,{pos1[[1]]+1,posnminus[[1]]-1}],posnminus[[1]]==pos1[[1]]+1,{}];
\[Gamma]={\[Alpha],\[Beta]};
Return[\[Gamma]]
]

TrToKK[\[Sigma]_]:=(*for KK basis ending in n-1,n fixed and 1 fixed in BCJ*)
Module[{n,nminus,\[Alpha],\[Beta],\[Beta]T,\[Beta]len,\[Gamma]},
n=Length[\[Sigma]];
nminus=n-1;
\[Gamma]=KK\[Alpha]\[Beta][\[Sigma]];
\[Alpha]=\[Gamma][[1]];
\[Beta]=\[Gamma][[2]];
\[Beta]len=Length[\[Beta]];
\[Beta]T=Reverse[\[Beta]];
Map[Join[#,{nminus,n}]&,OP[\[Alpha],\[Beta]T]]
]

KKtoBCJ[\[Sigma]_]:=(*for KK basis ending in n-1,n fixed and 1 fixed in BCJ*)
Module[{n,\[Alpha],\[Beta],\[Gamma],\[Alpha]len,\[Beta]len,BCJ,expr},
Clear[a,b,c];
n=Length[\[Sigma]];
\[Gamma]=BCJ\[Alpha]\[Beta][\[Sigma]];
\[Alpha]=\[Gamma][[1]];
\[Beta]=\[Gamma][[2]];
\[Alpha]len=Length[\[Alpha]];
\[Beta]len=Length[\[Beta]];
SetDirectory[Directory[]];
BCJ=ReadList["BCJ_formulas"];
expr=Which[n==4,
Which[\[Alpha]len==1,a= \[Alpha][[1]];BCJ[[1]],
\[Alpha]len==0,a=\[Beta][[1]];BCJ[[2]]],
n==5,
Which[
\[Alpha]len==2,a=\[Alpha][[1]]; b=\[Alpha][[2]]; BCJ[[3]],
\[Alpha]len==1,a=\[Alpha][[1]]; b=\[Beta][[1]]; BCJ[[4]],
\[Alpha]len==0,a=\[Beta][[1]];b=\[Beta][[2]];BCJ[[5]]],
n==6,
Which[
\[Alpha]len==3,a=\[Alpha][[1]]; b=\[Alpha][[2]]; c=\[Alpha][[3]]; BCJ[[6]],
\[Alpha]len==2,a=\[Alpha][[1]]; b=\[Alpha][[2]]; c=\[Beta][[1]]; BCJ[[7]],
\[Alpha]len==1,a=\[Alpha][[1]]; b=\[Beta][[1]]; c=\[Beta][[2]]; BCJ[[8]],
\[Alpha]len==0,a=\[Beta][[1]]; b=\[Beta][[2]]; c=\[Beta][[3]];BCJ[[9]]]
];
Clear[a,b,c];
expr/.Subscript[s, \[Alpha]_]:>Subscript[s, Sort[\[Alpha]]]
]

TrToBCJ[\[Sigma]_]:=(*for KK basis ending in n-1,n fixed and 1 fixed in BCJ*)
Module[{n,KKset,\[Beta]len,BCJset},
\[Beta]len=Length[KK\[Alpha]\[Beta][\[Sigma]][[2]]];
KKset=TrToKK[\[Sigma]];
BCJset=Map[KKtoBCJ[#]&, KKset];
(-1)^\[Beta]len*Total[BCJset]
]

CycOrderingR[set_]:=(*for KK basis ending in n,n-1 fixed and 1 fixed in BCJ*)
Module[{n,cycles},
n=Length[set];
cycles=SortBy[Permute[set,CyclicGroup[n]],Last];
cycles[[n-1]]
]

KK\[Alpha]\[Beta]R[set_]:=(*for KK basis ending in n,n-1 fixed and 1 fixed in BCJ*)
Module[{n,nminus,posn,posnminus,\[Alpha],\[Beta],\[Gamma],set1},
set1=CycOrderingR[set];
n=Length[set];
nminus=n-1;
posn=Flatten[ Position[set1,n]];
posnminus=Flatten[ Position[set1,nminus]];
\[Alpha]=Take[set1,posn[[1]]-1];
\[Beta]=Which[posnminus[[1]]>posn[[1]]+1,Take[set1,{posn[[1]]+1,posnminus[[1]]-1}],posnminus[[1]]==posn[[1]]+1,{}];
\[Gamma]={\[Alpha],\[Beta]};
Return[\[Gamma]]
]

BCJ\[Alpha]\[Beta]R[set_]:=(*for KK basis ending in n,n-1 fixed and 1 fixed in BCJ*)
Module[{n,nminus,pos1,posn,\[Alpha],\[Beta],\[Gamma]},
n=Length[set];
nminus=n-1;
pos1=Flatten[ Position[set,1]];
posn=Flatten[ Position[set,n]];
\[Alpha]=Take[set,pos1[[1]]-1];
\[Beta]=Which[posn[[1]]>pos1[[1]]+1,Take[set,{pos1[[1]]+1,posn[[1]]-1}],posn[[1]]==pos1[[1]]+1,{}];
\[Gamma]={\[Alpha],\[Beta]};
Return[\[Gamma]]
]

TrToKKR[\[Sigma]_]:=(*for KK basis ending in n,n-1 fixed and 1 fixed in BCJ*)
Module[{n,nminus,\[Alpha],\[Beta],\[Beta]T,\[Beta]len,\[Gamma]},
n=Length[\[Sigma]];
nminus=n-1;
\[Gamma]=KK\[Alpha]\[Beta]R[\[Sigma]];
\[Alpha]=\[Gamma][[1]];
\[Beta]=\[Gamma][[2]];
\[Beta]len=Length[\[Beta]];
\[Beta]T=Reverse[\[Beta]];
Map[Join[#,{n,nminus}]&,OP[\[Alpha],\[Beta]T]]
]

KKtoBCJR[\[Sigma]_]:=(*for KK basis ending in n,n-1 fixed and 1 fixed in BCJ*)
Module[{n,\[Alpha],\[Beta],\[Gamma],\[Alpha]len,\[Beta]len,BCJR,expr},
n=Length[\[Sigma]];
\[Gamma]=BCJ\[Alpha]\[Beta]R[\[Sigma]];
\[Alpha]=\[Gamma][[1]];
\[Beta]=\[Gamma][[2]];
\[Alpha]len=Length[\[Alpha]];
\[Beta]len=Length[\[Beta]];
SetDirectory[Directory[]];
BCJR=ReadList["BCJR_formulas"];
Clear[a,b,c];
expr=Which[n==4,
Which[\[Alpha]len==1,a= \[Alpha][[1]];BCJR[[1]],
\[Alpha]len==0,a=\[Beta][[1]]; BCJR[[2]]],
n==5,
Which[
\[Alpha]len==2,a=\[Alpha][[1]]; b=\[Alpha][[2]]; BCJR[[3]],
\[Alpha]len==1,a=\[Alpha][[1]]; b=\[Beta][[1]]; BCJR[[4]],
\[Alpha]len==0,a=\[Beta][[1]];b=\[Beta][[2]];BCJR[[5]]],
n==6,
Which[
\[Alpha]len==3,a=\[Alpha][[1]]; b=\[Alpha][[2]]; c=\[Alpha][[3]]; BCJR[[6]],
\[Alpha]len==2,a=\[Alpha][[1]]; b=\[Alpha][[2]]; c=\[Beta][[1]]; BCJR[[7]],
\[Alpha]len==1,a=\[Alpha][[1]]; b=\[Beta][[1]]; c=\[Beta][[2]]; BCJR[[8]],
\[Alpha]len==0,a=\[Beta][[1]]; b=\[Beta][[2]]; c=\[Beta][[3]];BCJR[[9]]]
];
Clear[a,b,c];
expr/.Subscript[s, \[Alpha]_]:>Subscript[s, Sort[\[Alpha]]]
]

TrToBCJR[\[Sigma]_]:=(*for KK basis ending in n,n-1 fixed and 1 fixed in BCJ*)
Module[{n,KKset,\[Beta]len,BCJset},
\[Beta]len=Length[KK\[Alpha]\[Beta]R[\[Sigma]][[2]]];
KKset=TrToKKR[\[Sigma]];
BCJset=Map[KKtoBCJR[#]&, KKset];
(-1)^\[Beta]len*Total[BCJset]
]



(*double partial amplitudes*)
TrToBCJ[\[Sigma]_,\[Delta]_]:=Module[{n,BCJL,BCJR,a,b,thing,expr},
(*remember you can check form using Clear[m]*)
n=Length[\[Sigma]];
BCJL=TrToBCJ[\[Sigma]]/. A[\[Alpha]_]:>a[\[Alpha]];
BCJR=TrToBCJR[\[Delta]]/.A[\[Beta]_]:>b[\[Beta]];
expr=Expand[BCJR*BCJL]/.a[\[Alpha]_]b[\[Beta]_]:>S[\[Alpha],\[Beta]];
expr/.S[\[Alpha]_,\[Beta]_]:>S[Table[\[Alpha][[i]],{i,2,n-2}],Table[\[Beta][[i]],{i,2,n-2}]]
]


(*minimal basis*) (*code from: *)
SetAttributes[MP,Orderless];
MP[p1_Plus,p2_]:=Map[MP[#,p2]&,p1];
MP[p1_,num__ p2_?LVecQ]:=num MP[p1,p2];
MP[p1_,num__?(FreeQ[#,_?LVecQ]&) p2_Plus]:=num MP[p1,p2];
MP[p_?NullLVecQ,p_?NullLVecQ]:=0;
MP[p1:{__},p2:{__}]:=p1 . p2-2p1[[1]]p2[[1]];
MP2[p_]:=MP[p,p];
MP2[p:{__}]:=p . p-2p[[1]]^2;

PBasis[pList_]:=Module[{n,pp,ret},n=Length[pList];
pp[i_,j_]:=MP[pList[[i]],pList[[j]]];
ret=Table[pp[1,i],{i,3,n-1}];(*Fix p1.p2 using -m^2=pn^2=(p1+p2+...)^2*)
Join[ret,Flatten[Table[pp[i,j],{i,2,n-2},{j,i+1,n-1}]]](*Use momentum convservation 0=sum_{j=1...n} (pj.pi) to fix pn.pi=-(p1.pi+p2.pi...)*)
(*The diagonal is fixed via pi^2=-m^2.*)];

RepPAnalytical[pList_,m_]:=Module[{n,pp,ret},n=Length[pList];
pp[i_,j_]:=MP[pList[[i]],pList[[j]]];
ret=Table[pp[i,i]->-m^2,{i,1,n}];(*The diagonal is fixed via pi^2=-m^2.*)
AppendTo[ret,pp[1,2]->m^2 (n-2)/2-Sum[pp[1,j],{j,3,n-1}]-Sum[pp[i,j],{i,2,n-1},{j,i+1,n-1}]];(*Fix p1.p2 using -m^2=pn^2=(p1+p2+...)^2*)
ret=Flatten[Join[ret,Table[pp[n,i]->-Sum[pp[j,i],{j,1,n-1}]/.ret,{i,1,n-1}]]];(*Use momentum convservation 0=sum(pi.pj) to fix pn.pi=-(p1.pi+p2.pi...)*)
DeleteCases[ret,0->0]
(*If m=0 and pi is a NullLVec then MP[p1,p1] is 0 automatically so you don't want to add the rule 0\[Rule]0*)];


(*functions for comparing to m[\[Alpha],\[Beta]] from s.mizera code 1610.04230*)

MandToMP[expr_]:=expr/.Subscript[s, \[Alpha]_]:> Module[{subs}, subs=Subsets[\[Alpha],{2}];Total[2*Map[MP[q[#[[1]]],q[#[[2]]]]&,subs]]]

CheckDoublePartial[n_,expr1_,expr2_]:=
Module[{rules,minbasis,ex1,ex2},
rules=RepPAnalytical[Map[q,Range[n]],0];
minbasis=PBasis[Map[q,Range[n]]];
ex1=MandToMP[expr1]/.rules;
ex2=MandToMP[expr2]/.rules;
Refine[Equal[ex1,ex2],minbasis\[Element]Reals]
]

CheckAllDP[n_]:=
Module[{leftPerms, rightPerms,dp},
leftPerms=Map[Join[#,{n}]&,Permutations[Range[n-1]]];
rightPerms=Map[Join[#,{n-1}]&,Permutations[DeleteCases[Range[n],n-1]]];
dp=Tuples[{leftPerms,rightPerms}];
Map[CheckDoublePartial[n,m[#[[1]],#[[2]]]/.Subscript[s, \[Alpha]__]-> \!\(\*SubscriptBox[\(s\), \({\[Alpha]}\)]\),-1*TrToBCJ[#[[1]],#[[2]]]]&,dp]
]

CFTrace[\[Delta]_]:=Module[{colorfactors},
colorfactors=Tr[Fold[NonCommutativeMultiply,Map[T[#]&,\[Delta]]]
]]

MandToPP[expr_]:=expr/.Subscript[s, \[Alpha]_]:> Module[{subs}, subs=Subsets[\[Alpha],{2}];Total[2*Map[pp[#[[1]],#[[2]]]&,subs]]]

BASPartialAmp[\[Sigma]_]:=Module[{n,perms,amps},
n=Length[\[Sigma]];
perms=Permutations[Range[n-1]];
perms=Map[Join[#,{n}]&,perms];
amps=Total[Map[CFTrace[#]*FullSimplify[TrToBCJ[\[Sigma],#]]&,perms]];
MandToPP[amps]
]
