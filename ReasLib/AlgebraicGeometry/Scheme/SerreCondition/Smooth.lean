/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.SerreCondition
public import ReasLib.AlgebraicGeometry.Scheme.Depth
public import Mathlib.CategoryTheory.ObjectProperty.SiteLocal
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.Basic

/-!
# Smooth-locality of Serre's conditions

This file records smooth-locality for schemes that are locally Noetherian and satisfy
Serre's conditions `(S_k)` or `(R_k)`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.satisfiesSerreConditionS

/-- For every `k`, being locally Noetherian and satisfying `(S_k)` is local for the
smooth precoverage. -/
instance smoothLocal (k : ℕ) :
    ObjectProperty.IsLocal
      (fun X : AlgebraicGeometry.Scheme.{u} ↦
        AlgebraicGeometry.IsLocallyNoetherian X ∧
          AlgebraicGeometry.Scheme.satisfiesSerreConditionS X k)
      AlgebraicGeometry.Scheme.bigSmoothPrecoverage := sorry

end AlgebraicGeometry.Scheme.satisfiesSerreConditionS

namespace AlgebraicGeometry.Scheme.satisfiesSerreConditionR

/-- For every `k`, being locally Noetherian and satisfying `(R_k)` is local for the smooth
precoverage. -/
instance smoothLocal (k : ℕ) :
    ObjectProperty.IsLocal
      (fun X : AlgebraicGeometry.Scheme.{u} ↦
        AlgebraicGeometry.IsLocallyNoetherian X ∧
          AlgebraicGeometry.Scheme.satisfiesSerreConditionR X k)
      AlgebraicGeometry.Scheme.bigSmoothPrecoverage := sorry

end AlgebraicGeometry.Scheme.satisfiesSerreConditionR
