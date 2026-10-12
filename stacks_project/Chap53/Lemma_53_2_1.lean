/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.Curve

public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 53.2.1 -/
@[stacks 0BXY] #check (AlgebraicGeometry.Curve.exists_openExtensionAtClosedPoint :
    ∀ {k : Type u} [Field k] (X Y : SchemeOverField k) [Curve X] [Variety Y] [IsProper Y.hom]
    (U : X.left.Opens) [Nonempty U] (f : Over.mk (U.ι ≫ X.hom) ⟶ Y)
    (x : X.left) (hx : x ∈ closedPoints X.left),
    let F := X.left.presheaf
    ∀ [IsDiscreteValuationRing (F.stalk x)],
    ∃ (U' : X.left.Opens) (hUU' : U ≤ U') (_ : x ∈ U')
      (f' : Over.mk (U'.ι ≫ X.hom) ⟶ Y),
      (Over.homMk (X.left.homOfLE hUU') (X.left.homOfLE_ι_assoc hUU' X.hom) :
        Over.mk (U.ι ≫ X.hom) ⟶ Over.mk (U'.ι ≫ X.hom)) ≫ f' = f)
