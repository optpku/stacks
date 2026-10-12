/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Hom
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Pullback

/-!
# Morphisms from pulled-back scheme pre-relations

This module constructs the canonical morphism from the pullback of a scheme pre-relation
along a morphism over the base to the original pre-relation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- The canonical morphism from the pullback of `P` along `g` to `P`. -/
def pullbackHom {S : Scheme.{u}} {U U' : Over S} (P : PreRelation U) (g : U' ⟶ U) :
    Hom (P.pullback g) P :=
  Hom.ofDefiningMap g (Limits.pullback.fst P.hom (prod.map g g)) (by
    rw [P.pullback_hom g]
    exact Limits.pullback.condition.symm)

/-- The canonical pullback morphism uses `g` on objects and the first pullback projection
on arrows. -/
theorem pullbackHom_spec {S : Scheme.{u}} {U U' : Over S} (P : PreRelation U)
    (g : U' ⟶ U) :
    (P.pullbackHom g).obj = g ∧
      (P.pullbackHom g).arrow = Limits.pullback.fst P.hom (prod.map g g) := by
  constructor <;> rfl

end AlgebraicGeometry.Scheme.PreRelation
