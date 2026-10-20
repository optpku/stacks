module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Locus.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.ClosedPoint.Specialization.Chain
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.BaseChange

/-!
# Flatness in sufficiently large dimensions

This module defines flatness of a scheme module over a base in dimensions at least a fixed
natural number and gives its pointwise characterization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}}

/-- A scheme module is flat over the base in dimensions at least `n` when every point where
flatness fails has residue-field transcendence degree less than `n` over its image. -/
def flatOverInDimensionsGE (ℱ : X.Modules) (f : X ⟶ S) (n : ℕ) : Prop :=
  ∀ x : X, ¬ flatOverAt ℱ f x → f.residueFieldTranscendenceDegreeAt x < (n : ℕ∞)

/-- The pointwise residue-field characterization of flatness over the base in dimensions at
least `n`. -/
theorem flatOverInDimensionsGE_iff (ℱ : X.Modules) (f : X ⟶ S) (n : ℕ) :
    flatOverInDimensionsGE ℱ f n ↔
      ∀ x : X, ¬ flatOverAt ℱ f x → f.residueFieldTranscendenceDegreeAt x < (n : ℕ∞) := sorry

/-- Flatness over the base in dimensions at least `n` is equivalent to every fibrewise
nonflat locus having topological Krull dimension less than `n`. -/
theorem flatOverInDimensionsGE_iff_fiberNonflatLocus_dim_lt
    (ℱ : X.Modules) (f : X ⟶ S)
    [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (n : ℕ) :
    flatOverInDimensionsGE ℱ f n ↔
      ∀ s : S, topologicalKrullDim (fiberNonflatLocus ℱ f s) < (n : WithBot ℕ∞) := sorry

/-- Flatness over the base in dimensions at least `n` is preserved by arbitrary scheme
base change. -/
theorem flatOverInDimensionsGE_pullback {S' : Scheme.{u}}
    (ℱ : X.Modules) (f : X ⟶ S)
    [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (n : ℕ) (g : S' ⟶ S) (h : flatOverInDimensionsGE ℱ f n) :
    flatOverInDimensionsGE (baseChangeModule f g ℱ) (pullback.snd f g) n := sorry

end AlgebraicGeometry.Scheme.Modules
