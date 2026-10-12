/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap61.«61_5_2_4_Stage»
public import stacks_project.Chap61.«61_5_2_5_WLocalization»

/-!
# Vanishing-pattern stage transitions

For finite `E₁ ⊆ E₂ ⊆ A`, the canonical stage map `A_{E₁} → A_{E₂}` induces an
affine scheme morphism `X_{E₂} ⟶ X_{E₁}` which sends `Z_{E₂}` into `Z_{E₁}`.
-/

@[expose] public section

open AlgebraicGeometry Algebra.WLocalHull CategoryTheory

universe u

namespace Algebra.WLocalHull

variable {A : Type u} [CommRing A]

/-- The canonical `A`-algebra transition `A_{E₁} → A_{E₂}` underlying the
stage ring map. -/
noncomputable def algHom {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) :
    stage A E₁ →ₐ[A] stage A E₂ where
  toRingHom := stageMap A h
  commutes' := sorry

/-- 61.5.2.4: the affine scheme morphism `X_{E₂} ⟶ X_{E₁}` induced by the
canonical `A`-algebra map `A_{E₁} → A_{E₂}` for finite `E₁ ⊆ E₂ ⊆ A`. -/
@[stacks 0972]
noncomputable def spectrumMap {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) :
    spectrum A E₂ ⟶ spectrum A E₁ :=
  Spec.map (CommRingCat.ofHom (stageMap A h))

/-- `spectrumMap` is `Spec.map` of the underlying ring homomorphism of `stageMap`. -/
theorem spectrumMap_eq {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) :
    spectrumMap h = Spec.map (CommRingCat.ofHom (stageMap A h)) :=
  sorry

/-- `spectrumMap` is `Spec.map` of the `A`-algebra transition. -/
theorem spectrumMap_algHom {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) :
    spectrumMap h = Spec.map (CommRingCat.ofHom (algHom h).toRingHom) :=
  sorry

/-- The identity subset induces the identity `A`-algebra map. -/
theorem algHom_id (E : Finset A) : algHom (Finset.Subset.refl E) = AlgHom.id A (stage A E) :=
  sorry

/-- Transition maps of stage algebras compose. -/
theorem algHom_comp {E₁ E₂ E₃ : Finset A} (h₁₂ : E₁ ⊆ E₂) (h₂₃ : E₂ ⊆ E₃) :
    (algHom h₂₃).comp (algHom h₁₂) = algHom (h₁₂.trans h₂₃) :=
  sorry

/-- The identity subset induces the identity scheme morphism. -/
theorem spectrumMap_id (E : Finset A) : spectrumMap (Finset.Subset.refl E) = 𝟙 (spectrum A E) :=
  sorry

/-- Transition maps of stage spectra compose. -/
theorem spectrumMap_comp {E₁ E₂ E₃ : Finset A} (h₁₂ : E₁ ⊆ E₂) (h₂₃ : E₂ ⊆ E₃) :
    spectrumMap h₂₃ ≫ spectrumMap h₁₂ = spectrumMap (h₁₂.trans h₂₃) :=
  sorry

/-- Stage algebra maps commute with the structure maps from `A`. -/
theorem algHom_commutes {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) :
    (algHom h).comp (Algebra.ofId A (stage A E₁)) = Algebra.ofId A (stage A E₂) :=
  sorry

/-- Any `A`-algebra map of stratum localizations equals `specializingMap`. -/
theorem specializingMap_unique {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) (p : Pattern A E₂)
    (f : specializingLocalization A (Pattern.restrict A E₁ p).elem
        (Pattern.restrict A E₁ p).span →ₐ[A]
      specializingLocalization A p.elem p.span) :
    f.toRingHom = specializingMap A h p :=
  sorry

/-- The morphism `X_{E₂} ⟶ X_{E₁}` sends `Z_{E₂}` into `Z_{E₁}`. -/
theorem mapsTo_closed {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) :
    Set.MapsTo (spectrumMap h) (Set.range (closedHom A E₂)) (Set.range (closedHom A E₁)) :=
  sorry

/-- The covariant functor of stage algebras on finite subsets of `A`. -/
noncomputable def ringFunctor (A : Type u) [CommRing A] : Finset A ⥤ CommRingCat.{u} where
  obj E := .of (stage A E)
  map f := CommRingCat.ofHom (stageMap A (leOfHom f))
  map_id _ := sorry
  map_comp _ _ := sorry

/-- The contravariant functor of stage spectra on finite subsets of `A`. -/
noncomputable def spectrumFunctor (A : Type u) [CommRing A] :
    (Finset A)ᵒᵖ ⥤ Scheme.{u} :=
  (ringFunctor A).op ⋙ Scheme.Spec

end Algebra.WLocalHull
