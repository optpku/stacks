module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologyBaseChange.Comparison

/-!
# Cohomology and base change criteria

This module relates pointwise cohomology base-change maps to their affine-local derived
comparison maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- For a cartesian square of schemes, pointwise cohomology base change is equivalent to
invertibility of the derived comparison on every compatible affine chart and on one
compatible affine cover. -/
theorem cohomologyBaseChange_tfae_affine
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g) (K : ModuleDerived.Quasicoherent X)
    (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') :
    let D := CohomologyBaseChangeModel.canonical g' f' f g sq
    List.TFAE
      [ ∀ (x' : X') (i : ℤ),
          IsIso (D.pointMap K K' α x' i)
      , ∀ c : AffineBaseChangeChart g' f' f g,
          IsIso (D.affineComparison K K' α c).map
      , ∃ cover : X'.AffineOpenCover,
          ∀ j : cover.I₀,
            ∃ c : AffineBaseChangeChart g' f' f g,
              (cover.f j).opensRange = (c.U' : X'.Opens) ∧
                IsIso (D.affineComparison K K' α c).map
      ] := sorry

/-- Pointwise cohomology base change is equivalent to invertibility of the comparison on
every compatible affine base-change chart. -/
theorem cohomologyBaseChange_pointwise_iff_affine
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g) (K : ModuleDerived.Quasicoherent X)
    (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') :
    let D := CohomologyBaseChangeModel.canonical g' f' f g sq
    (∀ (x' : X') (i : ℤ), IsIso (D.pointMap K K' α x' i)) ↔
      ∀ c : AffineBaseChangeChart g' f' f g,
        IsIso (D.affineComparison K K' α c).map := sorry

/-- Pointwise cohomology base change is equivalent to invertibility of the comparison on a
compatible affine open cover of the pullback scheme. -/
theorem cohomologyBaseChange_pointwise_iff_affineCover
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g) (K : ModuleDerived.Quasicoherent X)
    (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') :
    let D := CohomologyBaseChangeModel.canonical g' f' f g sq
    (∀ (x' : X') (i : ℤ), IsIso (D.pointMap K K' α x' i)) ↔
      ∃ cover : X'.AffineOpenCover,
        ∀ j : cover.I₀,
          ∃ c : AffineBaseChangeChart g' f' f g,
            (cover.f j).opensRange = (c.U' : X'.Opens) ∧
              IsIso (D.affineComparison K K' α c).map := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh

end
