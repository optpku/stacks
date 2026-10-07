module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Pullback.Opens

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraicGeometry

/- Lemma 26.17.3: compatible restrictions of the factors and base define
an open subspace of the scheme fibre product. -/
@[stacks 01JR] #check Scheme.Pullback.mapResLE
@[stacks 01JR] #check Scheme.Pullback.mapResLE_fst
@[stacks 01JR] #check Scheme.Pullback.mapResLE_snd
@[stacks 01JR] #check Scheme.Pullback.mapResLE_isOpenImmersion
@[stacks 01JR] #check Scheme.Pullback.opensRange_mapResLE
