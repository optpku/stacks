module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Definition
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Tower Transport of Homotopy-Limit Presentations

This leaf transports an explicit homotopy-limit presentation, and the intrinsic
homotopy-limit predicate, along an isomorphism of sequential inverse systems.
Transport receives the target product cone explicitly, so it reconstructs
neither a product instance nor a selected inverse locally.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u v

namespace CategoryTheory.HomotopyLimit

open SequentialInverseSystem.Milnor

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

namespace Presentation.TowerIso

/-- The explicit isomorphism between the source and target product-cone points induced by an
isomorphism of sequential inverse systems. -/
@[stacks 08TC]
def productIso {K L : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) (Q : LimitCone (Discrete.functor L.family)) (e : K ≅ L) :
    P.product.cone.pt ≅ Q.cone.pt :=
  ProductCone.mapIso P.product Q e

/-- The forward morphism of the product-point isomorphism is the explicit product-cone map. -/
@[simp]
theorem productIso_hom {K L : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) (Q : LimitCone (Discrete.functor L.family)) (e : K ≅ L) :
    (productIso P Q e).hom = ProductCone.map P.product Q e.hom := sorry

/-- The inverse morphism of the product-point isomorphism is the explicit reverse
product-cone map. -/
@[simp]
theorem productIso_inv {K L : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) (Q : LimitCone (Discrete.functor L.family)) (e : K ≅ L) :
    (productIso P Q e).inv = ProductCone.map Q P.product e.inv := sorry

/-- The inclusion into the target product cone used when transporting a presentation along a
tower isomorphism. -/
def inclusion {K L : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) (Q : LimitCone (Discrete.functor L.family)) (e : K ≅ L) :
    X ⟶ Q.cone.pt :=
  P.ι ≫ ProductCone.map P.product Q e.hom

/-- The connecting morphism from the target product cone used when transporting a presentation
along a tower isomorphism. -/
def connecting {K L : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) (Q : LimitCone (Discrete.functor L.family)) (e : K ≅ L) :
    Q.cone.pt ⟶ X⟦(1 : ℤ)⟧ :=
  ProductCone.map Q P.product e.inv ≫ P.connecting

/-- The tower-transport inclusion can equivalently be written using the forward morphism of
the explicit product-point isomorphism. -/
@[simp]
theorem inclusion_eq {K L : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) (Q : LimitCone (Discrete.functor L.family)) (e : K ≅ L) :
    inclusion P Q e = P.ι ≫ (productIso P Q e).hom := sorry

/-- The tower-transport connecting morphism can equivalently be written using the inverse
morphism of the explicit product-point isomorphism. -/
@[simp]
theorem connecting_eq {K L : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) (Q : LimitCone (Discrete.functor L.family)) (e : K ≅ L) :
    connecting P Q e = (productIso P Q e).inv ≫ P.connecting := sorry

/-- Transporting a homotopy-limit presentation along a tower isomorphism and a supplied target
product cone preserves distinguishedness of its Milnor triangle. -/
@[stacks 08TC]
theorem distinguished {K L : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) (Q : LimitCone (Discrete.functor L.family)) (e : K ≅ L) :
    Triangle.mk (inclusion P Q e) (ProductCone.difference L Q)
      (connecting P Q e) ∈ distTriang D := sorry

end Presentation.TowerIso

/-- Transport a homotopy-limit presentation along an isomorphism of sequential inverse systems,
using an explicitly supplied product cone for the target system. -/
@[stacks 08TC]
def Presentation.ofTowerIso {K L : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) (e : K ≅ L)
    (Q : LimitCone (Discrete.functor L.family)) : Presentation L X where
  product := Q
  ι := TowerIso.inclusion P Q e
  connecting := TowerIso.connecting P Q e
  distinguished := TowerIso.distinguished P Q e

/-- Tower transport stores the explicitly supplied target product cone. -/
@[simp]
theorem Presentation.ofTowerIso_product {K L : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) (e : K ≅ L)
    (Q : LimitCone (Discrete.functor L.family)) :
    (P.ofTowerIso e Q).product = Q := sorry

/-- Projections after tower transport are exactly those of the supplied target product cone. -/
@[simp]
theorem Presentation.ofTowerIso_projection {K L : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) (e : K ≅ L)
    (Q : LimitCone (Discrete.functor L.family)) (n : ℕ) :
    (P.ofTowerIso e Q).projection n = ProductCone.projection Q n := sorry

/-- The inclusion after tower transport is the original inclusion followed by the explicit
product-cone map. -/
@[simp]
theorem Presentation.ofTowerIso_ι {K L : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) (e : K ≅ L)
    (Q : LimitCone (Discrete.functor L.family)) :
    (P.ofTowerIso e Q).ι = P.ι ≫ ProductCone.map P.product Q e.hom := sorry

/-- The connecting morphism after tower transport is precomposed with the explicit reverse
product-cone map. -/
@[simp]
theorem Presentation.ofTowerIso_connecting
    {K L : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) (e : K ≅ L)
    (Q : LimitCone (Discrete.functor L.family)) :
    (P.ofTowerIso e Q).connecting =
      ProductCone.map Q P.product e.inv ≫ P.connecting := sorry

/-- Stage projections after tower transport are the original stage projections followed by the
corresponding component of the tower isomorphism. -/
@[simp, reassoc]
theorem Presentation.ofTowerIso_stageProjection
    {K L : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) (e : K ≅ L)
    (Q : LimitCone (Discrete.functor L.family)) (n : ℕ) :
    (P.ofTowerIso e Q).stageProjection n =
      P.stageProjection n ≫ e.hom.app (op n) := sorry

namespace IsOf

namespace TowerIso

/-- A homotopy-limit predicate transports along a tower isomorphism when a target product cone
is supplied explicitly. -/
@[stacks 08TC]
theorem ofProduct {K L : SequentialInverseSystem D} {X : D}
    (h : HomotopyLimit.IsOf K X) (e : K ≅ L)
    (Q : LimitCone (Discrete.functor L.family)) : HomotopyLimit.IsOf L X := sorry

end TowerIso

/-- The homotopy-limit predicate is stable under an isomorphism of sequential inverse systems. -/
@[stacks 08TC]
theorem ofTowerIso {K L : SequentialInverseSystem D} {X : D}
    (h : HomotopyLimit.IsOf K X) (e : K ≅ L) : HomotopyLimit.IsOf L X := sorry

end IsOf

end CategoryTheory.HomotopyLimit
