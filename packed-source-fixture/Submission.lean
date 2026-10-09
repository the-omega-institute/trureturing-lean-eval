import Submission.PackedEntry
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
load_packed_fixture "{Wp48S^xk9=GL@E0stWaAOHXW35cb3;3xkBbzJ}#3)}>NP%<X&9eo?~^2;;q?D#kE>ehOIebXCOACgF6WgA^bq*Nt#;nI>6N->#jq2gsMJ|sexkec|hW`Tg_$<8U1NHQvDiX2~)ctqltc*-9g7QnZ*&DDl#_?h3v^<TpJdU_7tC+lV;?Xp$leeC3mCkPcz%^qj(q)YxGGAnowX))QS+YcF8PZLE{lp(Y1D<=MhZK6i0dH+g8VVPkjHv2&{qFw~W?`AkGrmQZepf#e%Ja1Dh8|TAp&<+TJ;do38S<@uQ(KW;zbZayd{x>qInu8th#|~cUg3V5-&#90#4$R}*Do0;q!-k923B*SLq5`Zkm84|Z%8Ia4Y$fOs7XLuBr&)ppzpy`I<#V<9_>@|m&zCVYQPVobQ!3{LWo~bGI#&XH&6p+HA4sL?FHQ8tR`-T5XmqjEN}M^3{H5+ZZ=9`tc+otfar!r~W8861Wi)1)$_DEe7VY}!8hhNdAUDKZYo?_Vrst<D!((hN-M}y?Jogx9-_5S%<deH&5z^&?BbEjvAc!ysQZeUYDY!fCdEwlxzybkI;it~S5dDGI{NDHY;SF-d_Z{!yBjz*5zi%mep$!KdrP+IIAuYmTNIfJblFZ7Zg*VTiaqYlHQo9lrA30@^=WX^Ep2i1`oIKvtOEPJAMMZI%xq;6;qB8;}l&e?i@!c>JWmf?bc;xV4=uPuiak04J5u9DFy3RYJ@^y6Wc-T}oazm)%6YQAnbTy~Yw@O>ijQ)!hXg;DQ69+>2f~=_wlNN|ky#9!K34n@;1_vd8SxrvxnJ7-9{F>9Ytd92g&GtNgW@z16V0&Sb0nnDZ6Te%Lep~W{w)TxRH%uC@AXmcnb=wg~)Xs-|aPtlBQdyr{X+MGdoQRKh%=8x@?~my&?P<>bK(}wRhGvt!W#(Pl5k`2-P;_RZ(gngs0vp0Zs@g@DUnLf4U9X4+AllZkkIxuAjRY)~544Q@`tc(ieXb$~(o5+kZaWA6JqSFuol?&zci5HP$o|sU2V?3=zv3JrPVM3+^FiG>>`<jSy2PK2#|f;aQ#Jq!k<6AAiX@&+uAyXF_i>Sj8d8KsK6Xd(%A;4T!n@;)kV|6>=dMz|t{@sZ;4Jheep{#~VsNhE&F~x4myVZbgF2N%#9%W300000T`9>ZG)QjG00EH)fKUJcpjE0SvBYQl0ssI200dcD"
namespace Submission
theorem root (n : Nat) : n = n := PackedB.root n
theorem dynamic_macro (n : Nat) : n = n := by packed_refl
end Submission
#print axioms Submission.root
#print axioms Submission.dynamic_macro
