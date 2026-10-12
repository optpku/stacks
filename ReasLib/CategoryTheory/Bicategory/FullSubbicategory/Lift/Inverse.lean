/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.Computations
public import ReasLib.CategoryTheory.Bicategory.StrictPseudofunctor.Inverse

/-!
# Strict inverses restricted to full subbicategories

This module transports equality-level inverse certificates through the canonical
`FullSubbicategory.map` construction.  It is the shared owner for restricting mutually inverse
strict pseudofunctors to object properties preserved in both directions.
-/

@[expose] public section

universe wA vA uA wD vD uD

namespace CategoryTheory.ObjectProperty.FullSubbicategory

open CategoryTheory.Bicategory

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {D : Type uD} [Bicategory.{wD, vD} D]
variable {Q : ObjectProperty A} {P : ObjectProperty D}

/-- Mutually inverse strict pseudofunctors restrict to mutually inverse maps between full
subbicategories whenever they preserve the selected object properties in both directions. -/
theorem map.isStrictInverse
    {F : StrictPseudofunctor A D} {G : StrictPseudofunctor D A}
    (h : StrictPseudofunctor.IsStrictInverse F G)
    (hF : ∀ X : A, Q X → P (F.obj X))
    (hG : ∀ X : D, P X → Q (G.obj X)) :
    StrictPseudofunctor.IsStrictInverse (map F hF) (map G hG) := sorry

end CategoryTheory.ObjectProperty.FullSubbicategory
