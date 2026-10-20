module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.WLocalHull.Transition
public import ReasLib.AlgebraicGeometry.WLocalHull.Stage

/-!
# Transitions of finite vanishing-pattern spectra

Refinement of finite subsets induces contravariant morphisms of stage spectra
preserving their distinguished closed loci.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Algebra.WLocalHull

variable {A : Type u} [CommRing A]

/-- The affine scheme morphism induced by the canonical algebra transition
associated to refinement of finite subsets. -/
@[stacks 0972]
noncomputable def spectrumMap {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) :
    spectrum A E₂ ⟶ spectrum A E₁ :=
  Spec.map (CommRingCat.ofHom (stageMap A h))

/-- The scheme transition is the spectrum map of the finite-stage ring transition. -/
theorem spectrumMap_eq {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) :
    spectrumMap h = Spec.map (CommRingCat.ofHom (stageMap A h)) :=
  rfl

/-- The scheme transition is the spectrum map of the finite-stage algebra transition. -/
theorem spectrumMap_algHom {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) :
    spectrumMap h = Spec.map (CommRingCat.ofHom (algHom h).toRingHom) :=
  rfl

/-- The identity subset induces the identity scheme morphism. -/
theorem spectrumMap_id (E : Finset A) : spectrumMap (Finset.Subset.refl E) = 𝟙 (spectrum A E) :=
  sorry

/-- Transition maps of stage spectra compose contravariantly. -/
theorem spectrumMap_comp {E₁ E₂ E₃ : Finset A} (h₁₂ : E₁ ⊆ E₂) (h₂₃ : E₂ ⊆ E₃) :
    spectrumMap h₂₃ ≫ spectrumMap h₁₂ = spectrumMap (h₁₂.trans h₂₃) :=
  sorry

/-- A transition of stage spectra maps the finer distinguished closed locus into
the coarser distinguished closed locus. -/
theorem mapsTo_closed {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) :
    Set.MapsTo (spectrumMap h) (Set.range (closedHom A E₂)) (Set.range (closedHom A E₁)) :=
  sorry

/-- The contravariant functor of stage spectra on finite subsets of a commutative ring. -/
noncomputable def spectrumFunctor (A : Type u) [CommRing A] :
    (Finset A)ᵒᵖ ⥤ Scheme.{u} :=
  (ringFunctor A).op ⋙ Scheme.Spec

end Algebra.WLocalHull
