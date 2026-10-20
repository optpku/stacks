/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import ReasLib.AlgebraicGeometry.WLocalHull.Transition

/-!
# Inverse systems of finite-stage affine schemes

The directed poset of finite subsets of a ring `A` indexes the inverse systems
`X_E = Spec(A_E)` and `Z_E = Spec(Γ(Z_E))`, using the stage algebras and
transition maps already owned by `Algebra.WLocalHull`.
-/

@[expose] public section

open CategoryTheory Limits Opposite AlgebraicGeometry CommRingCat
open Algebra.WLocalHull

noncomputable section

universe u

namespace AlgebraicGeometry.WLocal.Construction

variable (A : Type u) [CommRing A]

/-- The inverse system `E ↦ X_E` on `OrderDual (Finset A)`, obtained by
transporting `spectrumFunctor` along the equivalence
`OrderDual (Finset A) ≌ (Finset A)ᵒᵖ`. -/
def schemeFunctor : OrderDual (Finset A) ⥤ Scheme.{u} :=
  (orderDualEquivalence (Finset A)).functor ⋙ spectrumFunctor A

/-- Finite-stage spectra are affine. -/
instance isAffine_schemeFunctor_obj (E : OrderDual (Finset A)) :
    IsAffine ((schemeFunctor A).obj E) :=
  isAffine_Spec _

/-- The vanishing ideal of a restricted pattern is contained in that of the
finer pattern. -/
theorem span_le_of_restrict {E F : Finset A} (h : E ⊆ F) (q : Pattern A F) :
    (Pattern.restrict A E q).span ≤ q.span := by
  classical
  apply Ideal.span_mono
  intro element element_mem
  simp only [Pattern.restrict, Finset.mem_coe, Finset.mem_sdiff,
    Finset.mem_inter] at element_mem ⊢
  exact ⟨h element_mem.1, fun pattern_mem ↦ element_mem.2 ⟨element_mem.1, pattern_mem⟩⟩

/-- The image of the restricted standard-open generator is a unit on the finer
closed stratum. -/
theorem isUnit_closedComponent {E F : Finset A} (h : E ⊆ F) (q : Pattern A F) :
    IsUnit
      (((algebraMap (A ⧸ q.span) (stratumSections A q.elem q.span)).comp
          (Ideal.Quotient.factor (span_le_of_restrict A h q)))
        (Ideal.Quotient.mk (Pattern.restrict A E q).span (Pattern.restrict A E q).elem)) := by
  classical
  have generator_dvd : (Pattern.restrict A E q).elem ∣ q.elem :=
    Finset.prod_dvd_prod_of_subset (E ∩ q.1) q.1 (fun element ↦ element)
      Finset.inter_subset_right
  change IsUnit (algebraMap (A ⧸ q.span) (stratumSections A q.elem q.span)
    (Ideal.Quotient.mk q.span (Pattern.restrict A E q).elem))
  exact IsLocalization.Away.isUnit_of_dvd (Ideal.Quotient.mk q.span q.elem)
    (map_dvd (Ideal.Quotient.mk q.span) generator_dvd)

/-- The transition map of closed-stratum sections associated to
`Z(E'₂, E''₂) ⊆ Z(E'₁, E''₁)`. -/
def closedComponentMap {E F : Finset A} (h : E ⊆ F) (q : Pattern A F) :
    stratumSections A (Pattern.restrict A E q).elem (Pattern.restrict A E q).span →+*
      stratumSections A q.elem q.span :=
  IsLocalization.Away.lift
    (Ideal.Quotient.mk (Pattern.restrict A E q).span (Pattern.restrict A E q).elem)
    (isUnit_closedComponent A h q)

/-- Projection from a closed-stage algebra onto a vanishing-pattern factor. -/
def closedStage.eval {E : Finset A} (p : Pattern A E) :
    closedStage A E →+* stratumSections A p.elem p.span :=
  Pi.evalRingHom (fun q : Pattern A E ↦ stratumSections A q.elem q.span) p

/-- The transition map `Γ(Z_E) ⟶ Γ(Z_F)` of closed-stage algebras for `E ⊆ F`. -/
def closedMap {E F : Finset A} (h : E ⊆ F) :
    closedStage A E →+* closedStage A F :=
  RingHom.pi fun q =>
    (closedComponentMap A h q).comp (closedStage.eval A (Pattern.restrict A E q))

/-- The directed system of closed-stage algebras `E ↦ Γ(Z_E)`. -/
def closedStageRingFunctor : Finset A ⥤ CommRingCat.{u} where
  obj E := of (closedStage A E)
  map f := ofHom (closedMap A (leOfHom f))
  map_id _ := sorry
  map_comp _ _ := sorry

/-- The inverse system `E ↦ Z_E` on `(Finset A)ᵒᵖ`. -/
def closedSpectrumFunctor : (Finset A)ᵒᵖ ⥤ Scheme.{u} :=
  (closedStageRingFunctor A).op ⋙ Scheme.Spec

/-- The inverse system `E ↦ Z_E` on `OrderDual (Finset A)`. -/
def closedFunctor : OrderDual (Finset A) ⥤ Scheme.{u} :=
  (orderDualEquivalence (Finset A)).functor ⋙ closedSpectrumFunctor A

/-- Finite-stage closed subschemes are affine. -/
instance isAffine_closedFunctor_obj (E : OrderDual (Finset A)) :
    IsAffine ((closedFunctor A).obj E) :=
  isAffine_Spec _

/-- The product of the canonical surjections `A_Z^~ → (A ⧸ I)_f` is surjective. -/
theorem closedStageMap_surjective (E : Finset A) :
    Function.Surjective (closedStageMap A E) := sorry

/-- Finite-stage inclusions `Z_E ⟶ X_E` are closed immersions. -/
instance isClosedImmersion_closedHom (E : Finset A) :
    IsClosedImmersion (closedHom A E) :=
  IsClosedImmersion.spec_of_surjective (ofHom (closedStageMap A E))
    (closedStageMap_surjective A E)

/-- The natural transformation of inverse systems sending each `Z_E` into `X_E`. -/
def closedιNatTrans : closedFunctor A ⟶ schemeFunctor A where
  app E := closedHom A (OrderDual.ofDual E)
  naturality := sorry

end AlgebraicGeometry.WLocal.Construction
