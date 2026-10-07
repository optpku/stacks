module

public import Mathlib.Algebra.DirectSum.Basic
public import ReasLib.AlgebraicGeometry.CycleGroup
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction

/-!
# Total relative cycle groups

This file assembles relative cycle groups in all integer degrees and defines degreewise
pushforward on the resulting direct sum.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup

/-- Total relative cycle homology, graded by relative dimension. -/
abbrev Total {S : Scheme.{u}} (delta : S → ℤ) (X : Over S) : Type u :=
  DirectSum ℤ (fun d ↦ CycleGroup X.left (X.hom.relativeDimensionFunction delta) d)

/-- The total cycle carrier is the direct sum of its relative-dimension pieces. -/
theorem total_def {S : Scheme.{u}} (delta : S → ℤ) (X : Over S) :
    Total delta X =
      DirectSum ℤ (fun d ↦ CycleGroup X.left (X.hom.relativeDimensionFunction delta) d) := sorry

namespace Total

/-- Degreewise pushforward on total relative cycle homology. -/
noncomputable def map {S : Scheme.{u}} (delta : S → ℤ) {X Y : Over S}
    (f : X ⟶ Y) [QuasiCompact f.left] : Total delta X →+ Total delta Y :=
  DirectSum.map fun d ↦
    CycleGroup.mapHom f.left (X.hom.relativeDimensionFunction delta)
      (Y.hom.relativeDimensionFunction delta) d

/-- Total cycle pushforward acts degreewise on homogeneous cycles. -/
theorem map_of {S : Scheme.{u}} (delta : S → ℤ) {X Y : Over S}
    (f : X ⟶ Y) [QuasiCompact f.left] (d : ℤ)
    (a : CycleGroup X.left (X.hom.relativeDimensionFunction delta) d) :
    map delta f (DirectSum.of _ d a) =
      DirectSum.of _ d (CycleGroup.mapHom f.left (X.hom.relativeDimensionFunction delta)
        (Y.hom.relativeDimensionFunction delta) d a) := sorry

end Total

end AlgebraicGeometry.CycleGroup
