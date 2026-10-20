module

public import stacks_project.Chap104.Lemma_104_5_3_DerivedQCoh
public import stacks_project.Chap104.Lemma_104_5_3_Comparison
import StacksCheckRecall

/-!
# Lemma 104.5.3

For an algebraic stack `X`, with `P_X` the parasitic objects of
`LQCoh^{fbc}(𝒪_X)`, inverse image `g^* = g⁻¹` along the lisse-étale
(resp. flat-fppf) morphism of Lemma 103.14.2 sends `D_{LQCoh^{fbc}}` of the
large site into `D_QCoh` of the small site, vanishes iff the complex lies in
`D_{P_X}`, and is quasi-inverse to `Lg_!` after passage to the Verdier
quotient `D_QCoh(𝒪_X)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]

/- Lemma 104.5.3 (1): with `g` the lisse-étale morphism of Lemma 103.14.2,
derived `g^*` sends `D_{LQCoh^{fbc}(𝒪_X)}(X_étale, 𝒪_X)` into
`D_QCoh(𝒪_{X_lisse,étale})`. -/
@[stacks 07B9]
#check (lisseEtaleInverseImageDerived_maps_qcoh X)

/- Lemma 104.5.3 (2): with `g` the lisse-étale morphism of Lemma 103.14.2,
derived `g^*` of an object of `D_{LQCoh^{fbc}(𝒪_X)}(X_étale, 𝒪_X)` vanishes
iff the object lies in `D_{P_X}(X_étale, 𝒪_X)`. -/
@[stacks 07B9]
#check lisseEtaleInverseImageDerived_isZero_iff_derivedParasitic

/- Lemma 104.5.3 (3): with `g` the lisse-étale morphism of Lemma 103.14.2,
derived `Lg_!` sends `D_QCoh(𝒪_{X_lisse,étale})` into
`D_{LQCoh^{fbc}(𝒪_X)}(X_étale, 𝒪_X)`. -/
@[stacks 07B9]
#check (lisseEtaleLowerShriekDerived_maps_lqcohFbc X)

/- Lemma 104.5.3 (4): the induced functors `g^*` and `Lg_!` are mutually
inverse between `D_QCoh(𝒪_X)` and `D_QCoh(𝒪_{X_lisse,étale})`. -/
@[stacks 07B9]
#check (lisseEtaleDerivedQCohInverseImage.instIsEquivalence X)

/- Lemma 104.5.3 (5): with `g` the flat-fppf morphism of Lemma 103.14.2,
derived `g^*` sends `D_{LQCoh^{fbc}}(𝒪_X)` into
`D_QCoh(𝒪_{X_flat,fppf})`. -/
@[stacks 07B9]
#check (flatFppfInverseImageDerived_maps_qcoh X)

/- Lemma 104.5.3 (6): with `g` the flat-fppf morphism of Lemma 103.14.2,
derived `g^*` of an object of `D_{LQCoh^{fbc}}(𝒪_X)` vanishes iff the object
lies in `D_{P_X}(𝒪_X)`. -/
@[stacks 07B9]
#check flatFppfInverseImageDerived_isZero_iff_derivedParasitic

/- Lemma 104.5.3 (7): with `g` the flat-fppf morphism of Lemma 103.14.2,
derived `Lg_!` sends `D_QCoh(𝒪_{X_flat,fppf})` into
`D_{LQCoh^{fbc}}(𝒪_X)`. -/
@[stacks 07B9]
#check (flatFppfLowerShriekDerived_maps_lqcohFbc X)

/- Lemma 104.5.3 (8): the induced functors `g^*` and `Lg_!` are mutually
inverse between `D_QCoh(𝒪_X)` and `D_QCoh(𝒪_{X_flat,fppf})`. -/
@[stacks 07B9]
#check (flatFppfDerivedQCohInverseImage.instIsEquivalence X)

end AlgebraicGeometry.AlgebraicStack
