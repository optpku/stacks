module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Definition
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Presentations of Sequential Homotopy Limits

A `HomotopyLimit.Presentation` retains the chosen product cone and all three
morphisms of its Milnor triangle. Consumers can therefore use stable
projections and triangle data without installing or reconstructing a local
product instance.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u v

namespace CategoryTheory.HomotopyLimit

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- An explicit product cone and distinguished Milnor triangle presenting `X` as
a homotopy limit of the sequential inverse system `K`. -/
@[stacks 08TC]
structure Presentation (K : SequentialInverseSystem D) (X : D) where
  /-- The explicitly chosen product cone of the terms of `K`. -/
  product : LimitCone (Discrete.functor K.family)
  /-- The inclusion of the homotopy-limit object into the chosen product. -/
  ι : X ⟶ product.cone.pt
  /-- The connecting morphism from the product to the shift of the homotopy-limit object. -/
  connecting : product.cone.pt ⟶ X⟦(1 : ℤ)⟧
  /-- The Milnor triangle determined by the stored data is distinguished. -/
  distinguished :
    Triangle.mk ι (SequentialInverseSystem.Milnor.ProductCone.difference K product)
      connecting ∈ distTriang D

/-- The `n`th projection of the explicit product stored by a homotopy-limit presentation. -/
def Presentation.projection {K : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) (n : ℕ) : P.product.cone.pt ⟶ K.obj (op n) :=
  SequentialInverseSystem.Milnor.ProductCone.projection P.product n

/-- The canonical comparison from the presented homotopy-limit object to the `n`th stage. -/
@[stacks 08TC]
def Presentation.stageProjection {K : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) (n : ℕ) : X ⟶ K.obj (op n) :=
  P.ι ≫ P.projection n

/-- The distinguished triangle encoded by a homotopy-limit presentation. -/
@[stacks 08TC]
def Presentation.triangle {K : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) : Triangle D :=
  Triangle.mk P.ι
    (SequentialInverseSystem.Milnor.ProductCone.difference K P.product) P.connecting

/-- The first morphism of a presentation triangle is its stored inclusion. -/
@[simp]
theorem Presentation.triangle.mor₁ {K : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) : P.triangle.mor₁ = P.ι := sorry

/-- The second morphism of a presentation triangle is the Milnor difference on its stored
product cone. -/
@[simp]
theorem Presentation.triangle.mor₂ {K : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) :
    P.triangle.mor₂ =
      SequentialInverseSystem.Milnor.ProductCone.difference K P.product := sorry

/-- The third morphism of a presentation triangle is its stored connecting morphism. -/
@[simp]
theorem Presentation.triangle.mor₃ {K : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) : P.triangle.mor₃ = P.connecting := sorry

/-- The Milnor triangle encoded by a homotopy-limit presentation is distinguished. -/
@[stacks 08TC]
theorem Presentation.triangle.distinguished {K : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) : P.triangle ∈ distTriang D := sorry

/-- The stage comparison is the stored inclusion followed by the corresponding product
projection. -/
@[simp]
theorem Presentation.stageProjection_eq {K : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) (n : ℕ) :
    P.stageProjection n = P.ι ≫ P.projection n := sorry

/-- Stage comparisons of a homotopy-limit presentation commute with every transition map of
its inverse system. -/
@[reassoc]
theorem Presentation.stageProjection_comp_transitionMap
    {K : SequentialInverseSystem D} {X : D} (P : Presentation K X)
    {i j : ℕ} (h : i ≤ j) :
    P.stageProjection j ≫ K.transitionMap h = P.stageProjection i := sorry

/-- Stage comparisons of a homotopy-limit presentation commute with the successor transition
maps of its inverse system. -/
@[reassoc]
theorem Presentation.stageProjection_naturality {K : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) (n : ℕ) :
    P.stageProjection (n + 1) ≫ K.transitionMap (Nat.le_succ n) =
      P.stageProjection n := sorry

/-- The successor compatibility equation for the stage projections, in the form required by
`NatTrans.ofOpSequence`. -/
theorem Presentation.cone_naturality {K : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) (n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj X).map (homOfLE (Nat.le_add_right n 1)).op ≫
        P.stageProjection n =
      P.stageProjection (n + 1) ≫ K.transitionMap (Nat.le_add_right n 1) := sorry

/-- The canonical cone over an inverse system carried by a homotopy-limit presentation. -/
@[stacks 08TC]
def Presentation.cone {K : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) : Cone K where
  pt := X
  π := NatTrans.ofOpSequence (fun n ↦ P.stageProjection n) P.cone_naturality

/-- The point of the canonical cone of a homotopy-limit presentation is the presented
object. -/
@[simp]
theorem Presentation.cone_pt {K : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) : P.cone.pt = X := sorry

/-- The `n`th leg of the canonical cone is the `n`th stage projection of the presentation. -/
@[simp]
theorem Presentation.cone_π_app {K : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) (n : ℕ) :
    P.cone.π.app (op n) = P.stageProjection n := sorry

/-- An explicit homotopy-limit presentation determines the intrinsic predicate. -/
@[stacks 08TC]
theorem Presentation.isOf {K : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) : HomotopyLimit.IsOf K X := sorry

namespace IsOf

/-- The intrinsic homotopy-limit predicate is equivalent to the existence of an explicit
presentation. -/
@[stacks 08TC]
theorem nonemptyPresentation_iff {K : SequentialInverseSystem D} {X : D} :
    HomotopyLimit.IsOf K X ↔ Nonempty (Presentation K X) := sorry

/-- An intrinsic homotopy-limit witness supplies a presentation nonemptily, without choosing a
public presentation. -/
theorem nonemptyPresentation {K : SequentialInverseSystem D} {X : D}
    (h : HomotopyLimit.IsOf K X) : Nonempty (Presentation K X) := sorry

/-- Nonempty explicit presentation data implies the intrinsic homotopy-limit predicate. -/
theorem ofNonemptyPresentation {K : SequentialInverseSystem D} {X : D}
    (h : Nonempty (Presentation K X)) : HomotopyLimit.IsOf K X := sorry

end IsOf

end CategoryTheory.HomotopyLimit
