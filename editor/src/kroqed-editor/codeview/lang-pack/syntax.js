// This file was generated by lezer-generator. You probably shouldn't edit it.
import {LRParser, LocalTokenGroup} from "@lezer/lr"
import {TakeInput} from "./externalTokens"
export const parser = LRParser.deserialize({
  version: 14,
  states: "'tQYQQOOO!yOPO'#CaOOQO'#Ca'#CaO#OO`O'#CaO#TO`O'#CaO#YO`O'#CaO#_O`O'#CaO#dO`O'#CaO#iO`O'#CaO#nO`O'#CaO#sO`O'#CaO#xO`O'#CaO#}O`O'#CaO$SQQO'#C`OOQO'#Cg'#CgQYQQOOO$XOQO,58{O$^O`O,58{O$cOSO,58{O$hOSO,58{O$mOQO,58{O$xOSO,58{O$}OSO,58{O%SOWO,58{O%XOSO,58{O%dOQO,58{O%iOQO,58{O%nOpO'#CdOOQO,58z,58zOOQO-E6e-E6eO%sO`O1G.gOOQO1G.g1G.gO%xO`O1G.gO%}O`O1G.gO&SO`O1G.gO&XOpO,59OO&^O`O7+$RO&cOQO7+$RO&kOQO7+$RO&pOQO7+$ROOQO1G.j1G.jOOQO<<Gm<<GmO&xO`O<<GmO&}O`O<<GmO'SOQOAN=XO'XOQOAN=XOOQOG22sG22sO'^O`OG22sO'cOQOLD(_O'hO`O!$'KyO'mOQO!)9AeOOQO!.K7P!.K7P",
  stateData: "'r~O^OSQOS~O_POaQObQOcQOdQOeQOfROgROhROiSOkROlROmROnROoROpROqROrTOtUOvVOxWO|XO!OYO!UZO!X[O~OP`O~OUaO~OUbO~OUcO~OUdO~OUeO~OUfO~OUgO~OUhO~OUiO~OUjO~O!ZkO~O`nO~OVoO~OjoO~OsnO~OunOznO{nO~OwnO~OynO~O}nO~O!PpO!SqO!TqO~O!VrO~O!YqO~OXsO~OUtO~OUuO~OUvO~OUwO~OYxO~OVyO~O!QyO!RzO~O!QyO~O!R{O!WzO~OU|O~OU}O~O!Q!OO~O!W!PO~OU!QO~O!R!RO~OU!SO~O!Q!TO~O",
  goto: "n[PPPP]aPPePPhT^O_T]O_Rl]Q_ORm_",
  nodeNames: "⚠ TakeInput Comment Program Sentence WaterproofTactic TacticInput dotSpace Lemma LemmaStatement dotSpace",
  maxTerm: 57,
  skippedNodes: [0,2],
  repeatNodeCount: 1,
  tokenData: "!(R~RdXY!aYZ!a]^!apq!fxy%iyz&r![!]0{!c!d1Q!d!e2k!e!f4W!f!g6u!g!h7p!j!k;y!k!l<h!n!oBX!q!rBv!u!vDo!v!wEj!w!xFR!y!zFjS!fO^Sl!kS^Syz!w![!]#S#T#U#g#]#^%WW!zP!O!P!}W#SOjWh#VP!_!`#Yh#_PyWpq#b`#gO}`W#jP#V#W#mW#pP#V#W#sW#vP#c#d#yW#|P#f#g$PW$SP#W#X$VW$YP#]#^$]W$`P#b#c$cW$fP#Z#[$iW$lPpq$oW$rP#h#i$uW$xP#c#d${W%OPpq%RW%WOwWW%ZP#b#c%^W%aPpq%dW%iOsW~%lQvw%rz{%}~%uPpq%x~%}Oi~~&QTOz%}z{&a{;'S%};'S;=`&l<%lO%}~&dPyz&g~&lOQ~~&oP;=`<%l%}~&uQpq&{!O!P0v~'OUxy'b#T#U'g#U#V(U#]#^(y#c#d-|#k#l.e~'gO!R~~'jP#b#c'm~'pP#W#X's~'vPpq'y~'|Pxy(P~(UO!W~~(XP#c#d([~(_P#h#i(b~(eP#[#](h~(kPpq(n~(qPxy(t~(yO!V~[(|P#h#i)P[)SPpq)V[)YQ#[#])`#g#h*{[)cP#c#d)f[)iP#`#a)l[)oP#W#X)r[)uP#g#h)x[){Ppq*O[*RP#h#i*U[*XP#[#]*[[*_P#T#U*b[*eP#h#i*h[*kPpq*n[*sP{Sxy*vW*{O!PW[+OP#i#j+R[+UP#Y#Z+X[+[P#Y#Z+_[+bP#]#^+e[+hP#V#W+k[+nP#X#Y+q[+tP#g#h+w[+zPpq+}[,QP#h#i,T[,WP#c#d,Z[,^Ppq,a[,dP#g#h,g[,jP#[#],m[,pP#c#d,s[,vP#k#l,y[,|Ppq-P[-SP#h#i-V[-YP#[#]-][-`P#T#U-c[-fP#h#i-i[-lPpq-o[-tPuSxy-wW-|O!TW~.PP#f#g.S~.VPpq.Y~.]Pxy.`~.eO!Y~[.hP#X#Y.k[.nPpq.q[.tP#V#W.w[.zP#c#d.}[/QP#b#c/T[/WP#V#W/Z[/^P#`#a/a[/dP#i#j/g[/jP#W#X/m[/pP#X#Y/s[/vPpq/y[/|P#h#i0P[0SP#[#]0V[0YP#T#U0][0`P#h#i0c[0fPpq0i[0nPzSxy0qW0vO!SW~0{O!Q~~1QO`~~1TP#g#h1W~1ZP#g#h1^~1aP#i#j1d~1gP#a#b1j~1mP#X#Y1p~1sPpq1v~1yP#h#i1|~2PP#[#]2S~2VP#T#U2Y~2]P#h#i2`~2cPpq2f~2kOh~~2nQ#X#Y2t#m#n3u~2wP#V#W2z~2}P#T#U3Q~3TP#i#j3W~3ZP#g#h3^~3aP#X#Y3d~3gPpq3j~3mPxy3p~3uO!U~~3xPpq3{~4OPxy4R~4WOt~~4ZQ#[#]4a#c#d5U~4dP#c#d4g~4jP#c#d4m~4pP#g#h4s~4vP#X#Y4y~4|Ppq5P~5UOx~~5XP#b#c5[~5_P#h#i5b~5eP#f#g5h~5kP#T#U5n~5qP#W#X5t~5wP#]#^5z~5}P#V#W6Q~6TP#h#i6W~6ZP#]#^6^~6aP#c#d6d~6gP#b#c6j~6mP!O!P6p~6uOc~~6xP#X#Y6{~7OP#Y#Z7R~7UP#]#^7X~7[P#b#c7_~7bP#X#Y7e~7hPpq7k~7pO|~~7sQ#]#^7y#l#m8t~7|P#h#i8P~8SP#[#]8V~8YP#X#Y8]~8`P#f#g8c~8fPpq8i~8lPxy8o~8tO!X~~8wP#d#e8z~8}P#T#U9Q~9TP#b#c9W~9ZP#W#X9^~9aPpq9d~9gP#h#i9j~9mP#[#]9p~9sP#X#Y9v~9yPpq9|~:PP#W#X:S~:VP#X#Y:Y~:]P#Y#Z:`~:cP#]#^:f~:iP#b#c:l~:oP#]#^:r~:uP#h#i:x~:{P#]#^;O~;RP#c#d;U~;XP#b#c;[~;_Ppq;b~;eP#c#d;h~;kP#Y#Z;n~;qPpq;t~;yOr~~;|P#X#Y<P~<SP#`#a<V~<YP#d#e<]~<`P!O!P<c~<hOa~~<kQ#b#c<q#h#i=l~<tP#W#X<w~<zP#X#Y<}~=QP#X#Y=T~=WP#W#X=Z~=^P|}=a~=dPpq=g~=lOp~~=oPpq=r~=uQ#[#]={#g#h?`~>OP#c#d>R~>UP#`#a>X~>[P#W#X>_~>bP#g#h>e~>hPpq>k~>nP#h#i>q~>tP#[#]>w~>zP#T#U>}~?QP#h#i?T~?WPpq?Z~?`Om~~?cP#i#j?f~?iP#Y#Z?l~?oP#Y#Z?r~?uP#]#^?x~?{P#V#W@O~@RP#X#Y@U~@XP#g#h@[~@_Ppq@b~@eP#h#i@h~@kP#c#d@n~@qPpq@t~@wP#g#h@z~@}P#[#]AQ~ATP#c#dAW~AZP#k#lA^~AaPpqAd~AgP#h#iAj~AmP#[#]Ap~AsP#T#UAv~AyP#h#iA|~BPPpqBS~BXOl~~B[P#X#YB_~BbP#a#bBe~BhP#a#bBk~BnP#T#UBq~BvO!Z~~ByP#U#VB|~CPP#h#iCS~CVP#T#UCY~C]P#]#^C`~CcP#b#cCf~CiPpqCl~CqPv~#g#hCt~CwP#i#jCz~C}P#V#WDQ~DTP#[#]DW~DZPpqD^~DaP#T#UDd~DgPpqDj~DoOk~~DrP#]#^Du~DxP#b#cD{~EOP#V#WER~EUP#X#YEX~E[PpqE_~EbPxyEe~EjO!O~~EmP#T#UEp~EsP#_#`Ev~EyP#X#YE|~FRO_~~FUP#g#hFX~F[P#X#YF_~FbPpqFe~FjOq~~FmP#X#YFp~FsPpqFv~FyT#T#UGY#V#WJX#b#cM`#g#h! o#i#j!%x~G]P#f#gG`~GcP#Z#[Gf~GiP#i#jGl~GoP#X#YGr~GuPpqGx~G{P#U#VHO~HRP#m#nHU~HXPpqH[~H_P#V#WHb~HeP#c#dHh~HkP#b#cHn~HqP#h#iHt~HwP#f#gHz~H}P#T#UIQ~ITP#W#XIW~IZP#]#^I^~IaP#V#WId~IgP#h#iIj~ImP#]#^Ip~IsP#c#dIv~IyP#b#cI|~JPP!O!PJS~JXOb~~J[Q#`#aJb#c#dKo~JeP#T#UJh~JkP#]#^Jn~JqP#a#bJt~JwPpqJz~J}P#h#iKQ~KTP#[#]KW~KZP#T#UK^~KaP#h#iKd~KgPpqKj~KoOn~~KrP#b#cKu~KxP#V#WK{~LOP#`#aLR~LUP#i#jLX~L[P#W#XL_~LbP#X#YLe~LhPpqLk~LnP#h#iLq~LtP#[#]Lw~LzP#T#UL}~MQP#h#iMT~MWPpqMZ~M`Og~~McP#X#YMf~MiP#X#YMl~MoP#W#XMr~MuPpqMx~M{P#h#iNO~NRP#c#dNU~NXPpqN[~N_P#g#hNb~NeP#[#]Nh~NkP#c#dNn~NqP#k#lNt~NwPpqNz~N}P#h#i! Q~! TP#[#]! W~! ZP#T#U! ^~! aP#h#i! d~! gPpq! j~! oOf~~! rP#[#]! u~! xP#c#d! {~!!OP#k#l!!R~!!UPpq!!X~!![P#U#V!!_~!!bP#c#d!!e~!!hP#h#i!!k~!!nP#[#]!!q~!!tPpq!!w~!!zQ#W#X!#Q#g#h!$e~!#TP#]#^!#W~!#ZP#f#g!#^~!#aP#X#Y!#d~!#gP#V#W!#j~!#mP#h#i!#p~!#sP#]#^!#v~!#yP#c#d!#|~!$PP#b#c!$S~!$VP#g#h!$Y~!$]P!O!P!$`~!$eOe~~!$hP#h#i!$k~!$nP#T#U!$q~!$tP#h#i!$w~!$zP#X#Y!$}~!%QP#a#b!%T~!%WP#X#Y!%Z~!%^P#b#c!%a~!%dP#h#i!%g~!%jP#g#h!%m~!%pP!O!P!%s~!%xOd~~!%{P#g#h!&O~!&RP#X#Y!&U~!&XPpq!&[~!&_P#]#^!&b~!&eP#b#c!&h~!&kP#W#X!&n~!&qP#i#j!&t~!&wP#V#W!&z~!&}P#h#i!'Q~!'TP#]#^!'W~!'ZP#c#d!'^~!'aP#b#c!'d~!'gPpq!'j~!'mP#c#d!'p~!'sP#b#c!'v~!'yPpq!'|~!(ROo~",
  tokenizers: [TakeInput, 2, 3, 4, new LocalTokenGroup("h~RP!O!PU~ZSV~XYUYZU]^UpqU~", 23, 6), new LocalTokenGroup("h~RP!O!PU~ZSY~XYUYZU]^UpqU~", 23, 9)],
  topRules: {"Program":[0,3]},
  tokenPrec: 0
})
