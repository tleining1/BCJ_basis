(* ::Package:: *)

RepP[pList_,pListNew_]:=Module[{nLength,sLength,subsetsOld,subsetsNew, listP,tmpP,pOld,pNew,listE,tmpE,eOld,eNew,RepForward,RepBackward,qpOld,qpNew,qeOld,qeNew,tmpqE,tmpqP,listqE,listqP,peOld,peNew,listPE, tmpPE,permsOld,permsNew,pLength,qpeOld,qpeNew,listqPE,tmpqPE},nLength=Length[pList];
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
qpeNew=Join[Map[pe[0,#]&,pList],Map[pe[#,0]&,pListNew]];
qpOld=Map[pp[0,#]&,pList];
qpNew=Map[pp[0,#]&,pListNew];
qeOld=Map[ee[0,#]&,pList];
qeNew=Map[ee[0,#]&,pListNew];
listqE=Array[tmpqE[#]&,nLength];
listqP=Array[tmpqP[#]&,nLength];
listqPE=Array[tmpqPE[#]&,2*nLength];
RepForward=Join[MapThread[Rule,{pOld,listP}],MapThread[Rule,{eOld,listE}],MapThread[Rule,{qpOld,listqP}],MapThread[Rule,{qeOld,listqE}],MapThread[Rule,{peOld,listPE}],MapThread[Rule,{qpeOld,listqPE}]];
RepBackward=Join[MapThread[Rule,{listP,pNew}],MapThread[Rule,{listE,eNew}],MapThread[Rule,{listqP,qpNew}],MapThread[Rule,{listqE,qeNew}],MapThread[Rule,{listPE, peNew}],MapThread[Rule,{listqPE,qpeNew}]];
RepForward/.RepBackward]
