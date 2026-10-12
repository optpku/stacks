/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Cohomology.Vanishing
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped AlgebraicGeometry TensorProduct
noncomputable section
universe u

namespace AlgebraicGeometry.IsBlowup

/- Lemma 51.22.4 (1). If `d(Gr_I(A)) ≥ 1` and `q ≥ q(Gr_I(A))`, then the
degree-`d(Gr_I(A))` cohomology of `p^*M(q)` vanishes. -/
@[stacks 0GAA]
#check (AlgebraicGeometry.IsBlowup.topTwistCohomology_isZero :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (n c : ℕ) (hcn : c ≤ n)
    (M : ModuleCat (A ⧸ I ^ n)) [Module.Finite (A ⧸ I ^ n) M]
    (hM : Module.IsIdealProjective (Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) M)
    (q : ℤ) (hd : 1 ≤ associatedGradedFiberDimension I)
    (hq : (associatedGradedUniformityThreshold I : ℤ) ≤ q),
    IsZero (Scheme.Hom.cohomology p (quotientModuleTwist I p M q)
      (associatedGradedFiberDimension I)))

/- Lemma 51.22.4 (2). If `d(Gr_I(A)) ≥ 2` and `q ≥ q(Gr_I(A))`, then the
degree-`d(Gr_I(A)) - 1` cohomology of `p^*M(q)` vanishes. -/
@[stacks 0GAA]
#check (AlgebraicGeometry.IsBlowup.penultimateTwistCohomology_isZero :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (n c : ℕ) (hcn : c ≤ n)
    (M : ModuleCat (A ⧸ I ^ n)) [Module.Finite (A ⧸ I ^ n) M]
    (hM : Module.IsIdealProjective (Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) M)
    (q : ℤ) (hd : 2 ≤ associatedGradedFiberDimension I)
    (hq : (associatedGradedUniformityThreshold I : ℤ) ≤ q),
    IsZero (Scheme.Hom.cohomology p (quotientModuleTwist I p M q)
      (associatedGradedFiberDimension I - 1)))

/- Lemma 51.22.4 (3). In an intermediate positive degree, the canonical
transition by `(d(Gr_I(A)) - 1 - i)c` induces the zero map on cohomology. -/
@[stacks 0GAA]
#check (AlgebraicGeometry.IsBlowup.twistTransition_eq_zero :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (n c : ℕ) (hcn : c ≤ n)
    (M : ModuleCat (A ⧸ I ^ n)) [Module.Finite (A ⧸ I ^ n) M]
    (hM : Module.IsIdealProjective (Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) M)
    (i : ℕ) (q : ℤ) (hi : 0 < i)
    (hid : i < associatedGradedFiberDimension I - 1)
    (hq : (associatedGradedUniformityThreshold I : ℤ) +
      (((associatedGradedFiberDimension I - 1 - i) * c : ℕ) : ℤ) ≤ q),
    (Scheme.Hom.cohomologyFunctor p i).map
      (canonicalTwistTransition I p M q
        ((associatedGradedFiberDimension I - 1 - i) * c)) = 0)

/- Lemma 51.22.4 (4). If `i = 0`, `d ∈ {0, 1}`, and `q ≥ q₀`, there is a
surjection `I ^ q M ⟶ H⁰(X, p^*M(q))`.

Operator-authorized local erratum: replace the displayed `I ^ q M` by
`I ^ q ⊗[A] M`. The original uploaded text is retained unchanged. The proof
uses `(I ^ q / I ^ (q + n))` on a free `A / I ^ n` presentation, which induces
this tensor map. It does not descend to the product submodule in general. -/
@[stacks 0GAA]
#check (AlgebraicGeometry.IsBlowup.adicSection_surjective :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (n c : ℕ) (hcn : c ≤ n)
    (M : ModuleCat (A ⧸ I ^ n)) [Module.Finite (A ⧸ I ^ n) M]
    (hM : Module.IsIdealProjective (Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) M)
    (q : ℤ) (hd : associatedGradedFiberDimension I ≤ 1)
    (hq : (associatedGradedUniformityThreshold I : ℤ) ≤ q),
    Function.Surjective (canonicalAdicTensorSectionMap I p M q).hom)

/- Lemma 51.22.4 (5). If `i = 0`, `d > 1`, and
`q ≥ q₀ + (d - 1)c`, the image of
`H⁰(X, p^*M(q)) ⟶ H⁰(X, p^*M(q - (d - 1)c))` is contained in the image of
the canonical map `I ^ (q - (d - 1)c) M ⟶
H⁰(X, p^*M(q - (d - 1)c))`.

Operator-authorized local erratum: the comparison image is that of
`I ^ (q - (d - 1)c) ⊗[A] M`, using the same canonical tensor section map
as the corrected fourth clause. All numerical bounds and hypotheses are
unchanged; no identification with the product submodule is asserted. -/
@[stacks 0GAA]
#check (AlgebraicGeometry.IsBlowup.twistTransition_range_le :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (n c : ℕ) (hcn : c ≤ n)
    (M : ModuleCat (A ⧸ I ^ n)) [Module.Finite (A ⧸ I ^ n) M]
    (hM : Module.IsIdealProjective (Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) M)
    (q : ℤ) (hd : 1 < associatedGradedFiberDimension I)
    (hq : (associatedGradedUniformityThreshold I : ℤ) +
      (((associatedGradedFiberDimension I - 1) * c : ℕ) : ℤ) ≤ q),
    LinearMap.range ((Scheme.Hom.cohomologyFunctor p 0).map
      (canonicalTwistTransition I p M q
        ((associatedGradedFiberDimension I - 1) * c))).hom ≤
      LinearMap.range (canonicalAdicTensorSectionMap I p M
        (q - (((associatedGradedFiberDimension I - 1) * c : ℕ) : ℤ))).hom)

end AlgebraicGeometry.IsBlowup
