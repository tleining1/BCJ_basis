(* ::Package:: *)

Get["BCJNumeratorsMod.m"]
Get["DoublePartialBCJ.m"]



RepP[expr_,pList_,pListNew_]:=Module[{nLength,sLength,subsetsOld,subsetsNew, listP,tmpP,pOld,pNew,listE,tmpE,eOld,eNew,RepForward,RepBackward,qpOld,qpNew,qeOld,qeNew,tmpqE,tmpqP,listqE,listqP,peOld,peNew,listPE, tmpPE,permsOld,permsNew,pLength,qpeOld,qpeNew,listqPE,tmpqPE},nLength=Length[pList];
subsetsOld=Subsets[pList,{2}];
subsetsNew=Subsets[pListNew,{2}];
sLength=Length[subsetsOld];

pOld=Map[pp[#[[1]],#[[2]]]&,subsetsOld];
listP=Array[tmpP[#]&,sLength];
pNew=Map[pp[#[[1]],#[[2]]]&,subsetsNew];
eOld=Map[ee[#[[1]],#[[2]]]&,subsetsOld];
listE=Array[tmpE[#]&,sLength];
eNew=Map[ee[#[[1]],#[[2]]]&,subsetsNew];
permsOld=Permutations[pList,{2}];
permsNew=Permutations[pListNew,{2}];
peOld=Map[pe[#[[1]],#[[2]]]&,permsOld];
peNew =Map[pe[#[[1]],#[[2]]]&,permsNew];
pLength=Length[permsOld];
listPE=Array[tmpPE[#]&,pLength];
qpeOld=Join[Map[pe[0,#]&,pList],Map[pe[#,0]&,pList]];
qpeNew=Join[Map[pe[0,#]&,pListNew],Map[pe[#,0]&,pListNew]];
qpOld=Map[pp[0,#]&,pList];
qpNew=Map[pp[0,#]&,pListNew];
qeOld=Map[ee[0,#]&,pList];
qeNew=Map[ee[0,#]&,pListNew];
listqE=Array[tmpqE[#]&,nLength];
listqP=Array[tmpqP[#]&,nLength];
listqPE=Array[tmpqPE[#]&,2*nLength];
RepForward=Join[MapThread[Rule,{pOld,listP}],MapThread[Rule,{eOld,listE}],MapThread[Rule,{qpOld,listqP}],MapThread[Rule,{qeOld,listqE}],MapThread[Rule,{peOld,listPE}],MapThread[Rule,{qpeOld,listqPE}]];
RepBackward=Join[MapThread[Rule,{listP,pNew}],MapThread[Rule,{listE,eNew}],MapThread[Rule,{listqP,qpNew}],MapThread[Rule,{listqE,qeNew}],MapThread[Rule,{listPE, peNew}],MapThread[Rule,{listqPE,qpeNew}]];
expr/.RepForward/.RepBackward]


YMBCJ[\[Sigma]_]:=Module[{n,num},
n=Length[\[Sigma]];
num=RepP[K[n],Range[n],\[Sigma]];
num/.{pe[0,\[Alpha]_]:> \[Alpha]*0,pp[0,\[Alpha]_]->Which[\[Alpha]==n,1,\[Alpha]==\[Alpha],-1/(n-1)]}
]

NLSMBCJ[\[Sigma]_]:=Module[{n,YM,q},
n=Length[\[Sigma]];
YM=YMBCJ[\[Sigma]];
q=YM/.{pe[i_,j_]:>Which[j==n,0,j==j,pp[i,j]],ee[i_,j_]:>Which[j==n,-pp[0,i]/pp[0,n],i==n,-pp[0,j]/pp[0,n],i==i,0]};
q/.{pp[0,\[Alpha]_]:>Which[\[Alpha]==n,1,i==i,-1/(n-1)]}
]

YMAmp[n_]:=Module[{perms},
perms=Permutations[n-1];
perms=Map[Join[#,{n}]&,perms];
Total[Map[BASPartialAmp[#]*YMBCJ[#]&,perms]]
]

YMPartialAmp[\[Sigma]_]:=Module[{n,perms,\[Rho]},
\[Rho]=CycOrdering[\[Sigma]];
n=Length[\[Sigma]];
perms=Permutations[n-1];
perms=Map[Join[#,{n}]&,perms];
Total[Map[YMBCJ[#]*MandToPP[TrToBCJ[\[Rho],#]]&,perms]]
]

YMAmp2[n_]:=Module[{perms},
perms=Permutations[n-1];
perms=Map[Join[#,{n}]&,perms];
Total[Map[CFTrace[#]*YMPartialAmp[#]&,perms]]
]

GRPartialAmp[\[Sigma]_]:= (*not color ordered, but a sum over all 
permutataions up to cyclicity will give full amplitudes*)
Module[{n,perms,bars},
n=Length[\[Sigma]];
perms=Permutations[n-1];
perms=Map[Join[#,{n}]&,perms];
bars=YMBCJ[\[Sigma]]/.{ee :> OverBar[ee],pe :> OverBar[pe]};
Total[Map[TrToBCJ[\[Sigma],#]*bars*YMBCJ[#]&,perms]]]

GRAmp[n_]:=Module[{perms},
perms=Permutations[n-1];
perms=Map[Join[#,{n}]&,perms];
Total[Map[GRPartialAmp[#]&,perms]]
]

BIPartialAmp[\[Sigma]_]:= (*not color ordered, but a sum over all 
permutataions up to cyclicity will give full amplitudes*)
Module[{n,perms,bars},
n=Length[\[Sigma]];
perms=Permutations[n-1];
perms=Map[Join[#,{n}]&,perms];
bars=NLSMBCJ[\[Sigma]]/.{ee :> OverBar[ee],pe :> OverBar[pe]};
Total[Map[TrToBCJ[\[Sigma],#]*bars*YMBCJ[#]&,perms]]]

BIAmp[n_]:=Module[{perms},
perms=Permutations[n-1];
perms=Map[Join[#,{n}]&,perms];
Total[Map[BIPartialAmp[#]&,perms]]
]
