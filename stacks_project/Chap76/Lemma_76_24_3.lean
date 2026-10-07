module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Spec.IdealSubobject
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap76.Theorem_76_22_1

/-!
# Infinitesimal flatness over a Noetherian affine base

If an algebraic space is locally of finite presentation over the spectrum of a
Noetherian ring and a coherent module is relatively flat on every infinitesimal
neighbourhood of `V(I)`, then the relative-flat locus contains the preimage of
`V(I)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {A : Type u} [CommRing A]

/-- The closed immersion `Spec(A ⧸ I ^ n) ⟶ Spec A`. -/
def idealPowerQuotientMap (I : Ideal A) (n : ℕ) :=
  @Spec.quotientMap (CommRingCat.of A) (I ^ n)

/-- `idealPowerQuotientMap I n` is `Spec.quotientMap` of `I ^ n`. -/
theorem idealPowerQuotientMap_eq (I : Ideal A) (n : ℕ) :
    idealPowerQuotientMap I n = @Spec.quotientMap (CommRingCat.of A) (I ^ n) :=
  sorry

/-- The infinitesimal neighbourhood `S_n = Spec(A ⧸ I ^ n)`, as an algebraic space over
`Spec A`. -/
def idealPowerSpace (I : Ideal A) (n : ℕ) :
    AlgebraicSpace (Spec (CommRingCat.of A)) :=
  ofOver (Over.mk (idealPowerQuotientMap I n))

/-- `idealPowerSpace I n` is `ofOver` of the affine quotient closed immersion
`Spec(A ⧸ I ^ n) ⟶ Spec A`. -/
theorem idealPowerSpace_eq (I : Ideal A) (n : ℕ) :
    idealPowerSpace I n = ofOver (Over.mk (idealPowerQuotientMap I n)) :=
  sorry

/-- The closed immersion `S_n ⟶ S` induced by `A ⟶ A ⧸ I ^ n`. -/
def idealPowerι (I : Ideal A) (n : ℕ) :
    ofOver (Over.mk (idealPowerQuotientMap I n)) ⟶
      ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))) :=
  ofOverHomMk (idealPowerQuotientMap I n)
    (Category.comp_id (idealPowerQuotientMap I n))

/-- `idealPowerι I n` is `ofOverHomMk` of `idealPowerQuotientMap I n`. -/
theorem idealPowerι_eq (I : Ideal A) (n : ℕ) :
    idealPowerι I n =
      ofOverHomMk (idealPowerQuotientMap I n)
        (Category.comp_id (idealPowerQuotientMap I n)) :=
  sorry

/-- The infinitesimal fibre `X_n = S_n ×_S X`. -/
def idealPowerFiber (I : Ideal A) (X : AlgebraicSpace (Spec (CommRingCat.of A)))
    (n : ℕ) : AlgebraicSpace (Spec (CommRingCat.of A)) :=
  Limits.pullback (idealPowerι I n) (toBase X)

/-- `idealPowerFiber I X n` is the chosen fibre product of `idealPowerι I n` with
`toBase X`. -/
theorem idealPowerFiber_eq (I : Ideal A)
    (X : AlgebraicSpace (Spec (CommRingCat.of A))) (n : ℕ) :
    idealPowerFiber I X n = Limits.pullback (idealPowerι I n) (toBase X) :=
  sorry

/-- The pullback `F_n` of an `𝒪_X`-module to `X_n`. -/
def pullbackIdealPower (I : Ideal A) {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    (F : X.Modules) (n : ℕ) : (idealPowerFiber I X n).Modules :=
  (pullback (Limits.pullback.snd (idealPowerι I n) (toBase X))).obj F

/-- `pullbackIdealPower I F n` is module pullback of `F` along `X_n ⟶ X`. -/
theorem pullbackIdealPower_eq (I : Ideal A)
    {X : AlgebraicSpace (Spec (CommRingCat.of A))} (F : X.Modules) (n : ℕ) :
    pullbackIdealPower I F n =
      (pullback (Limits.pullback.snd (idealPowerι I n) (toBase X))).obj F :=
  sorry

/-- Lemma 76.24.3: Let `A` be a Noetherian ring and `I ⊆ A` an ideal. Let `X` be an
algebraic space locally of finite presentation over `S = Spec A`. For `n ≥ 1` set
`S_n = Spec(A ⧸ I ^ n)` and `X_n = S_n ×_S X`. Let `F` be a coherent `𝒪_X`-module.
If for every `n ≥ 1` the pullback `F_n` of `F` to `X_n` is flat over `S_n`, then the
open locus where `F` is flat over `S` contains the inverse image of `V(I)` under
`X ⟶ S`.

The official statement writes “pullback to `X`” and “flat over `X`”; the proof and
Algebra 10.99.11 show the intended maps are the pullback of `F` to `X_n` and the
open locus of flatness over `S`. -/
@[stacks 08VP]
theorem zeroLocus_preimage_subset_flatOverLocus [IsNoetherianRing A] (I : Ideal A)
    (X : AlgebraicSpace (Spec (CommRingCat.of A)))
    [LocallyOfFinitePresentation (toBase X)] (F : X.Modules) [F.IsCoherent]
    (hflat : ∀ n, 1 ≤ n →
      flatOver (pullbackIdealPower I F n)
        (Limits.pullback.fst (idealPowerι I n) (toBase X))) :
    Points.base ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) ⊆
      flatOverLocus F (toBase X) :=
  sorry

/-- If each infinitesimal pullback of `F` is relatively flat, then every point of `X`
over `V(I)` is a relative-flatness point of `F` over `S`. -/
theorem flatOverAt_of_mem_zeroLocus [IsNoetherianRing A] (I : Ideal A)
    (X : AlgebraicSpace (Spec (CommRingCat.of A)))
    [LocallyOfFinitePresentation (toBase X)] (F : X.Modules) [F.IsCoherent]
    (hflat : ∀ n, 1 ≤ n →
      flatOver (pullbackIdealPower I F n)
        (Limits.pullback.fst (idealPowerι I n) (toBase X)))
    {x : Points X} (hx : Points.base x ∈ PrimeSpectrum.zeroLocus (I : Set A)) :
    flatOverAt F (toBase X) x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
