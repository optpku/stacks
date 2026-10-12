/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap97.«97_5_0_1_OnObjects»

/-!
# Base change of limit-preserving-on-objects 1-morphisms

Limit preservation on objects for 1-morphisms of categories fibred in groupoids
over `(Sch/S)_fppf` is stable under 2-fibre-product base change.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

namespace AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects

/-- If `p : X ⟶ Y` is limit preserving on objects, then so is its base change
`TwoFibreProduct.fst q p : X ×_Y Z ⟶ Z` along any `q : Z ⟶ Y`. -/
instance pullback_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (p : X ⟶ Y) (q : Z ⟶ Y) [LimitPreservingOnObjects p] :
    LimitPreservingOnObjects (TwoFibreProduct.fst.{u + 1, u, u + 1, u} q p) :=
  sorry

end AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects
