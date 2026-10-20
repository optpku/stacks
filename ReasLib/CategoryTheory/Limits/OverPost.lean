module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.GuitartExact.Over
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Right adjoints in slice-product squares

This file owns the comparison between the right adjoints in the slice square
obtained by postcomposing along a functor that preserves binary products.
The existing `TwoSquare.overPost` namespace supplies the mathematical context,
so the public declarations do not repeat a slice- or product-specific prefix.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u1 u2 v1 v2

noncomputable section

namespace CategoryTheory.TwoSquare.overPost

variable {C : Type u1} [Category.{v1} C]
variable {D : Type u2} [Category.{v2} D]
variable (u : D ⥤ C)
variable [HasBinaryProducts C] [HasBinaryProducts D]

/-- The product comparison underlying the component of the right-adjoint comparison is compatible
with the structure maps to `u.obj V`. -/
theorem rightAdjointIsoApp_comm (V Y : D)
    [forall Z, PreservesLimit (pair V Z) u] :
    prodComparison u V Y ≫ ((Over.star (u.obj V)).obj (u.obj Y)).hom =
      u.map (((Over.star V).obj Y).hom) := sorry

/-- The component at `Y` of the comparison between the right adjoints in the slice-product
square induced by `u` and `V`. -/
noncomputable def rightAdjointIsoApp (V Y : D)
    [forall Z, PreservesLimit (pair V Z) u] :
    (Over.star V ⋙ Over.post u).obj Y ≅ (u ⋙ Over.star (u.obj V)).obj Y :=
  Over.isoMk ((prodComparisonNatIso u V).app Y) (rightAdjointIsoApp_comm u V Y)

/-- The components `rightAdjointIsoApp u V` are natural in the slice object. -/
theorem rightAdjointIsoApp_naturality (V : D)
    [forall Z, PreservesLimit (pair V Z) u]
    {Y Y' : D} (f : Y ⟶ Y') :
    (Over.star V ⋙ Over.post u).map f ≫ (rightAdjointIsoApp u V Y').hom =
      (rightAdjointIsoApp u V Y).hom ≫ (u ⋙ Over.star (u.obj V)).map f := sorry

/-- The canonical natural isomorphism between the right adjoints in the slice-product square
attached to a binary-product-preserving functor. -/
noncomputable def rightAdjointIso (V : D)
    [forall Y, PreservesLimit (pair V Y) u] :
    Over.star V ⋙ Over.post u ≅ u ⋙ Over.star (u.obj V) :=
  NatIso.ofComponents
    (fun Y => rightAdjointIsoApp u V Y)
    (fun {_ _} f => rightAdjointIsoApp_naturality u V f)

/-- Every component of the canonical right-adjoint comparison is an isomorphism in the relevant
slice category. -/
theorem rightAdjointIso_hom_app_isIso (V Y : D)
    [forall Z, PreservesLimit (pair V Z) u] :
    IsIso ((rightAdjointIso u V).hom.app Y) := sorry

end CategoryTheory.TwoSquare.overPost
