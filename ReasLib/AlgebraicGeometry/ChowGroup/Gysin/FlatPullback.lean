/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin
public import ReasLib.AlgebraicGeometry.CycleGroup.Reindex
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme.Pullback.Over

/-!
# Flat pullback and Gysin homomorphisms

This file records the compatibility of zero-scheme Gysin homomorphisms with flat
pullback.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Gysin pullback along the zero scheme of a section commutes with flat pullback,
where the pullback before Gysin is taken on cycles. -/
theorem gysin_flatPullback_eq_flatPullback_gysin
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X X' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    (f : X' ⟶ X) (r : ℕ) [Flat f.left] [Hom.RelativeDimension f.left r]
    (ℒ : X.left.Modules) [Invertible ℒ] (s : ℒ.sections) (k : ℤ)
    (α : CycleGroup X.left (X.hom.relativeDimensionFunction δ) (k + 1)) :
    gysin X'.hom δ ((pullback f.left).obj ℒ) (sectionsPullback f.left ℒ s)
        (k + (r : ℤ))
        (CycleGroup.reindex (X'.hom.relativeDimensionFunction δ)
          (add_right_comm k 1 (r : ℤ))
          (CycleGroup.flatPullback δ X' X f r (k + 1) α)) =
      @ChowGroup.flatPullback S _ δ _
        (Over.mk
          (zeroSchemeι ((pullback f.left).obj ℒ) (sectionsPullback f.left ℒ s) ≫ X'.hom))
        (Over.mk (zeroSchemeι ℒ s ≫ X.hom)) _ _
        (zeroSchemePullbackOverHom f ℒ s) r
        (zeroSchemePullbackOverHom_flat f ℒ s)
        (zeroSchemePullbackOverHom_relativeDimension f r ℒ s) k
        (gysin X.hom δ ℒ s k α) := sorry

end AlgebraicGeometry.Scheme.Modules
