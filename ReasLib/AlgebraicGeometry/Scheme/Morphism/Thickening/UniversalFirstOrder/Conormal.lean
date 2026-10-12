/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal

@[expose] public section

universe u

namespace AlgebraicGeometry.Thickening.IsUniversalFirstOrder

/-- The conormal sheaf of a universal first-order thickening of a formally unramified
morphism. -/
noncomputable def conormalSheaf {X : Scheme.{u}} (T : Thickening.Over X)
    [FormallyUnramified T.left.hom] [IsUniversalFirstOrder T] : T.left.left.Modules :=
  Scheme.Hom.conormalSheaf T.hom.left

/-- The conormal sheaf of a universal first-order thickening is the conormal sheaf of its
defining immersion. -/
theorem conormalSheaf_eq {X : Scheme.{u}} (T : Thickening.Over X)
    [FormallyUnramified T.left.hom] [IsUniversalFirstOrder T] :
    conormalSheaf T = Scheme.Hom.conormalSheaf T.hom.left := sorry

end AlgebraicGeometry.Thickening.IsUniversalFirstOrder
