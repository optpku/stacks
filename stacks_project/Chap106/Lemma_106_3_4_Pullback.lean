module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap106.Definition_106_3_1_Hom
public import stacks_project.Chap106.Definition_106_3_3_FirstOrderThickening

/-!
# Base change of thickenings of algebraic stacks

The chosen 2-fibre product of a thickening of algebraic stacks along an
arbitrary morphism of algebraic stacks is again a thickening, and the
resulting square is a morphism of thickenings. First-order thickenings are
likewise stable under this base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsThickening

/-- The 2-fibre-product projection `TwoFibreProduct.snd j f'` of a thickening
`j : Y ⟶ Y'` of algebraic stacks is a thickening. -/
instance twoFibreProduct_snd {S : Scheme.{u}} {Y Y' X' : GroupoidsOver S}
    [AlgebraicStack Y] [AlgebraicStack Y'] [AlgebraicStack X']
    (j : Y ⟶ Y') (f' : X' ⟶ Y') [IsThickening j]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} j f')] :
    IsThickening (TwoFibreProduct.snd.{u + 1, u, u + 1, u} j f') :=
  sorry

namespace Hom

/-- The chosen 2-fibre product of a thickening `j : Y ⟶ Y'` along a morphism
`f' : X' ⟶ Y'` of algebraic stacks yields a morphism of thickenings from
`TwoFibreProduct.snd j f'` to `j`. -/
noncomputable def pullback {S : Scheme.{u}} {Y Y' X' : GroupoidsOver S}
    [AlgebraicStack Y] [AlgebraicStack Y'] [AlgebraicStack X']
    (j : Y ⟶ Y') (f' : X' ⟶ Y') [IsThickening j]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} j f')] :
    Hom (TwoFibreProduct.snd.{u + 1, u, u + 1, u} j f') j
      (TwoFibreProduct.fst.{u + 1, u, u + 1, u} j f') f' :=
  mk (TwoFibreProduct.snd.{u + 1, u, u + 1, u} j f') j
    (TwoFibreProduct.fst.{u + 1, u, u + 1, u} j f') f'
    (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} j f')

/-- The square 2-isomorphism of `pullback j f'` is the canonical 2-fibre-product
comparison cell. -/
theorem pullback_w {S : Scheme.{u}} {Y Y' X' : GroupoidsOver S}
    [AlgebraicStack Y] [AlgebraicStack Y'] [AlgebraicStack X']
    (j : Y ⟶ Y') (f' : X' ⟶ Y') [IsThickening j]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} j f')] :
    (pullback j f').w =
      TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} j f' :=
  sorry

/-- `pullback j f'` is `Hom.mk` applied to the 2-fibre-product comparison
isomorphism. -/
theorem pullback_eq_mk {S : Scheme.{u}} {Y Y' X' : GroupoidsOver S}
    [AlgebraicStack Y] [AlgebraicStack Y'] [AlgebraicStack X']
    (j : Y ⟶ Y') (f' : X' ⟶ Y') [IsThickening j]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} j f')] :
    pullback j f' =
      mk (TwoFibreProduct.snd.{u + 1, u, u + 1, u} j f') j
        (TwoFibreProduct.fst.{u + 1, u, u + 1, u} j f') f'
        (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} j f') :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicStack.IsThickening

namespace AlgebraicGeometry.AlgebraicStack.IsFirstOrderThickening

/-- The 2-fibre-product projection `TwoFibreProduct.snd j f'` of a first-order
thickening `j : Y ⟶ Y'` of algebraic stacks is a first-order thickening. -/
instance twoFibreProduct_snd {S : Scheme.{u}} {Y Y' X' : GroupoidsOver S}
    [AlgebraicStack Y] [AlgebraicStack Y'] [AlgebraicStack X']
    (j : Y ⟶ Y') (f' : X' ⟶ Y') [IsFirstOrderThickening j]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} j f')] :
    IsFirstOrderThickening (TwoFibreProduct.snd.{u + 1, u, u + 1, u} j f') :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsFirstOrderThickening

