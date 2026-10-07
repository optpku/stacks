module

public import stacks_project.Chap104.Lemma_104_5_4_Colocalization
import StacksCheckRecall

/-!
# Lemma 104.5.4

For an algebraic stack `X` and `E` in `D_{LQCoh^{fbc}}(𝒪_X)`, there is a
canonical distinguished triangle `E' ⟶ E ⟶ P ⟶ E'⟦1⟧` in
`D_{LQCoh^{fbc}}(𝒪_X)` with `P` in `D_{Parasitic ∩ LQCoh^{fbc}}(𝒪_X)` and
`Hom_{D(𝒪_X)}(E', P') = 0` for every such `P'`. The canonical `E'` is
`Lg_! g^* E` along the flat-fppf morphism of Lemma 103.14.2.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open AlgebraicGeometry.GroupoidsOver

/- Lemma 104.5.4 (1): the counit `Lg_! g^* E ⟶ E` completes to a distinguished
triangle in `D_{LQCoh^{fbc}}(𝒪_X)` whose third vertex is parasitic. -/
@[stacks 07BA]
#check DerivedLQCohFbc.exists_colocalizationTriangle

/- Lemma 104.5.4 (2): `Hom_{D(𝒪_X)}(Lg_! g^* E, P') = 0` for every `P'` in
`D_{Parasitic ∩ LQCoh^{fbc}}(𝒪_X)`. -/
@[stacks 07BA]
#check DerivedLQCohFbc.colocalize_hom_eq_zero
