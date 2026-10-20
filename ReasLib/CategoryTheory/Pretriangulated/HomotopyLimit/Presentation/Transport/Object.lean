module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Definition
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Object Transport of Homotopy-Limit Presentations

This leaf transports an explicit homotopy-limit presentation, and the intrinsic
homotopy-limit predicate, along an isomorphism of the candidate first object.
The chosen product cone is retained unchanged.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u v

namespace CategoryTheory.HomotopyLimit

open SequentialInverseSystem.Milnor

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

namespace Presentation.ObjectIso

/-- The inclusion of a homotopy-limit presentation after replacing its first object by an
isomorphic object. -/
def inclusion {K : SequentialInverseSystem D} {X X' : D}
    (P : Presentation K X) (e : X ≅ X') : X' ⟶ P.product.cone.pt :=
  e.inv ≫ P.ι

/-- The connecting morphism after replacing the first object of a presentation by an
isomorphic object. -/
def connecting {K : SequentialInverseSystem D} {X X' : D}
    (P : Presentation K X) (e : X ≅ X') : P.product.cone.pt ⟶ X'⟦(1 : ℤ)⟧ :=
  P.connecting ≫ (shiftFunctor D (1 : ℤ)).map e.hom

/-- Replacing the first object of a homotopy-limit presentation by an isomorphic object
preserves distinguishedness of its Milnor triangle. -/
@[stacks 08TC]
theorem distinguished {K : SequentialInverseSystem D} {X X' : D}
    (P : Presentation K X) (e : X ≅ X') :
    Triangle.mk (inclusion P e) (ProductCone.difference K P.product)
      (connecting P e) ∈ distTriang D := sorry

end Presentation.ObjectIso

/-- Transport a homotopy-limit presentation along an isomorphism of its first object. The
chosen product cone is retained unchanged. -/
@[stacks 08TC]
def Presentation.ofObjectIso {K : SequentialInverseSystem D} {X X' : D}
    (P : Presentation K X) (e : X ≅ X') : Presentation K X' where
  product := P.product
  ι := ObjectIso.inclusion P e
  connecting := ObjectIso.connecting P e
  distinguished := ObjectIso.distinguished P e

/-- Object transport retains the chosen product cone. -/
@[simp]
theorem Presentation.ofObjectIso_product {K : SequentialInverseSystem D} {X X' : D}
    (P : Presentation K X) (e : X ≅ X') :
    (P.ofObjectIso e).product = P.product := sorry

/-- Object transport retains every projection of the chosen product cone. -/
@[simp]
theorem Presentation.ofObjectIso_projection {K : SequentialInverseSystem D} {X X' : D}
    (P : Presentation K X) (e : X ≅ X') (n : ℕ) :
    (P.ofObjectIso e).projection n = P.projection n := sorry

/-- The inclusion of an object-transported presentation is obtained by precomposing the
original inclusion with the inverse isomorphism. -/
@[simp]
theorem Presentation.ofObjectIso_ι {K : SequentialInverseSystem D} {X X' : D}
    (P : Presentation K X) (e : X ≅ X') :
    (P.ofObjectIso e).ι = e.inv ≫ P.ι := sorry

/-- The connecting morphism of an object-transported presentation is obtained by applying the
shift functor to the forward isomorphism. -/
@[simp]
theorem Presentation.ofObjectIso_connecting
    {K : SequentialInverseSystem D} {X X' : D}
    (P : Presentation K X) (e : X ≅ X') :
    (P.ofObjectIso e).connecting =
      P.connecting ≫ (shiftFunctor D (1 : ℤ)).map e.hom := sorry

/-- Stage projections after object transport are the original stage projections precomposed
with the inverse isomorphism. -/
@[simp, reassoc]
theorem Presentation.ofObjectIso_stageProjection
    {K : SequentialInverseSystem D} {X X' : D}
    (P : Presentation K X) (e : X ≅ X') (n : ℕ) :
    (P.ofObjectIso e).stageProjection n = e.inv ≫ P.stageProjection n := sorry

namespace IsOf

/-- The homotopy-limit predicate is stable under an isomorphism of its candidate first object. -/
@[stacks 08TC]
theorem ofObjectIso {K : SequentialInverseSystem D} {X X' : D}
    (h : HomotopyLimit.IsOf K X) (e : X ≅ X') : HomotopyLimit.IsOf K X' := sorry

end IsOf

end CategoryTheory.HomotopyLimit
