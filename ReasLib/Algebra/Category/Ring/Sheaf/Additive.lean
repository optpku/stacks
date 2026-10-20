module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Topology.Sheaves.Abelian

/-!
# Additive sheaves

Underlying additive sheaves and additive evaluation differences for sheaves of commutative rings.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : TopCat.{u}}

/-- The additive sheaf underlying a sheaf of commutative rings. -/
abbrev additiveSheaf (A : X.Sheaf CommRingCat.{u}) :
    X.Sheaf AddCommGrpCat.{u} :=
  (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).obj A

/-- The morphism of additive sheaves underlying a morphism of commutative-ring sheaves. -/
abbrev additiveSheafMap {A B : X.Sheaf CommRingCat.{u}}
    (g : A ⟶ B) : additiveSheaf A ⟶ additiveSheaf B :=
  (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).map g

/-- The additive difference of two morphisms into a common sheaf of commutative rings. -/
noncomputable abbrev additiveEvaluationDifference {A B : X.Sheaf CommRingCat.{u}}
    (evalA evalB : A ⟶ B) : additiveSheaf A ⟶ additiveSheaf B :=
  additiveSheafMap evalA + (-additiveSheafMap evalB)

/-- On sections, an additive evaluation difference is the difference of the two values. -/
theorem additiveEvaluationDifference_app {A B : X.Sheaf CommRingCat.{u}}
    (evalA evalB : A ⟶ B) (U : (Opens X)ᵒᵖ) (h : A.1.obj U) :
    (additiveEvaluationDifference evalA evalB).hom.app U h =
      evalA.hom.app U h - evalB.hom.app U h := sorry

end AlgebraicGeometry
