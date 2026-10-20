/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import ReasLib.CategoryTheory.MorphismProperty.Localization.RightFraction.Quotient

/-!
# Explicit right-fraction Hom-colimit presentation

For a morphism property with a right calculus of fractions, source denominators form a cofiltered
category, so their opposite gives the filtered orientation of the Hom-colimit formula. The
computational root is the explicit right-fraction quotient; the comparison with an arbitrary
localization model is obtained afterwards from the universal localization equivalence.
-/

@[expose] public section

universe v u

namespace CategoryTheory
namespace MorphismProperty

open Limits

variable {C : Type u} [Category.{v} C]

/- The existing full subcategory `MorphismProperty.Over W ⊤ X` owns the source-denominator
category. Thus an object is a denominator
`s : X' ⟶ X` with `W s`, while a morphism is an arbitrary map
`a : X' ⟶ X''` making the triangle

```
                    a
       X' ─────────────────▶ X''
        ╲                    ╱
       s ╲                  ╱ t
          ╲                ╱
           └──────▶ X ◀───┘
```

commute, i.e. `a ≫ t = s`. The opposite category `(MorphismProperty.Over W ⊤ X)ᵒᵖ` therefore has
the filtered orientation needed for the Hom-colimit.

The computational root below maps `Functor.ColimitType` directly to
`RightFraction.Localization.Hom W X Y`, the explicit quotient by
`RightFractionRel`. Both directions are quotient maps. The model-independent
comparison is then transported along `Localization.homEquiv`, so no inverse
function chooses a fraction representative of an arbitrary localized morphism. -/

namespace RightFraction

/-- If `W` has a right calculus of fractions, the category `MorphismProperty.Over W ⊤ X` of denominators
`s : X' ⟶ X` in `W` and commutative triangles over `X` is cofiltered. -/
@[stacks 05Q4 "cofiltered category of source denominators"]
instance sourceArrows_isCofiltered
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions] (X : C) :
    IsCofiltered (MorphismProperty.Over W ⊤ X) := sorry
/- Proof strategy: apply `LeftFraction.targetArrows_isFiltered` to `W.op` and
`Opposite.op X`, then transport filteredness along the restriction of
`Under.opEquivOpOver X` identified by
`MorphismProperty.inverseImage_op_overObj`; equivalently, construct the three
cofilteredness fields from `W.id_mem`, the right Ore square, and
`HasRightCalculusOfFractions.ext`. -/

namespace Localization

variable (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
variable (X Y : C)

/-- The lifted Hom-diagram on source denominators: at
`s : (MorphismProperty.Over W ⊤ X)ᵒᵖ` its
value is `ULift (s.unop.left ⟶ Y)`, and a refinement acts by precomposition. -/
abbrev homDiagram : (MorphismProperty.Over W ⊤ X)ᵒᵖ ⥤ Type (max u v) :=
  (Over.forget W ⊤ X ⋙ CategoryTheory.Over.forget X).op ⋙
    uliftYoneda.{u}.obj Y

/-- The right fraction represented by a diagram element `f` at a source
denominator `s : (MorphismProperty.Over W ⊤ X)ᵒᵖ`. -/
def fraction (s : (MorphismProperty.Over W ⊤ X)ᵒᵖ) (f : (homDiagram W X Y).obj s) :
    W.RightFraction X Y :=
  RightFraction.mk s.unop.hom s.unop.prop f.down

/-- The canonical colimit representative of a right fraction, indexed by its
denominator and carrying its numerator. -/
def fractionToColimitType (z : W.RightFraction X Y) :
    (homDiagram W X Y).ColimitType :=
  (homDiagram W X Y).ιColimitType
    (Opposite.op (Over.mk (⊤ : MorphismProperty C) z.s z.hs)) (ULift.up z.f)

/-- Related right fractions determine the same canonical colimit representative. -/
theorem fractionToColimitType_eq_of_rel (z₁ z₂ : W.RightFraction X Y)
    (h : RightFractionRel z₁ z₂) :
    fractionToColimitType W X Y z₁ = fractionToColimitType W X Y z₂ := sorry
/- Proof strategy: unpack `h` as a common source `Z` with comparison maps
`t₁` and `t₂`; use the common denominator and its membership proof to form a
common `Over` index, then apply `Functor.ιColimitType_eq_of_map_eq_map` to the
two reversed triangles and the numerator equality in `h`. -/

/-- The cocone leg from a source-denominator numerator to the explicit right-fraction
quotient Hom-set. -/
def homCoconeApp (s : (MorphismProperty.Over W ⊤ X)ᵒᵖ) :
    (homDiagram W X Y).obj s → Hom W X Y :=
  fun f ↦ Hom.mk (fraction W X Y s f)

/-- The quotient-valued cocone legs respect reversed commutative triangles in
`(MorphismProperty.Over W ⊤ X)ᵒᵖ`. -/
theorem homCocone_naturality {s t : (MorphismProperty.Over W ⊤ X)ᵒᵖ} (a : s ⟶ t) :
    Function.comp (homCoconeApp W X Y t) ((homDiagram W X Y).map a) =
      homCoconeApp W X Y s := sorry
/- Proof strategy: use `Over.w a.unop`; the two resulting right fractions have a common source,
and then apply `Quot.sound` to their `RightFractionRel` witness. -/

/-- The concrete Type-valued cocone from `homDiagram W X Y` to the explicit right-fraction
quotient Hom-set. -/
def homCocone : (homDiagram W X Y).CoconeTypes where
  pt := Hom W X Y
  ι := homCoconeApp W X Y
  ι_naturality := homCocone_naturality W X Y

/-- The forward map from the source-denominator colimit quotient to right-fraction classes. -/
def colimitTypeToHom :
    (homDiagram W X Y).ColimitType → Hom W X Y :=
  (homDiagram W X Y).descColimitType (homCocone W X Y)

/-- The quotient-valued Hom-colimit map sends a diagram coprojection to its right-fraction
class. -/
@[simp]
theorem colimitTypeToHom.apply_ιColimitType (s : (MorphismProperty.Over W ⊤ X)ᵒᵖ)
    (f : (homDiagram W X Y).obj s) :
    colimitTypeToHom W X Y ((homDiagram W X Y).ιColimitType s f) =
      Hom.mk (fraction W X Y s f) := sorry

/-- The quotient-valued Hom-colimit map sends the canonical representative of a right fraction
to its class. -/
@[simp]
theorem colimitTypeToHom.apply_fractionToColimitType (z : W.RightFraction X Y) :
    colimitTypeToHom W X Y (fractionToColimitType W X Y z) = Hom.mk z := sorry

/-- The inverse map from a right-fraction quotient class to the source-denominator colimit
quotient. -/
def homToColimitType :
    Hom W X Y → (homDiagram W X Y).ColimitType :=
  Quot.lift (fractionToColimitType W X Y) (fractionToColimitType_eq_of_rel W X Y)

/-- The inverse Hom-colimit map sends a right-fraction class to its canonical colimit
representative. -/
@[simp]
theorem homToColimitType_mk (z : W.RightFraction X Y) :
    homToColimitType W X Y (Hom.mk z) = fractionToColimitType W X Y z := sorry

/-- `homToColimitType` is a left inverse to `colimitTypeToHom`. -/
theorem homColimitType_leftInverse (x : (homDiagram W X Y).ColimitType) :
    homToColimitType W X Y (colimitTypeToHom W X Y x) = x := sorry
/- Proof strategy: use `Functor.ιColimitType_jointly_surjective` to reduce to a diagram
coprojection, then identify the reconstructed denominator with the original index. -/

/-- `homToColimitType` is a right inverse to `colimitTypeToHom`. -/
theorem homColimitType_rightInverse (f : Hom W X Y) :
    colimitTypeToHom W X Y (homToColimitType W X Y f) = f := sorry
/- Proof strategy: quotient-induct on `f = Hom.mk z` and use the canonical representative
computation rule. -/

/-- The data-clean equivalence between the source-denominator colimit quotient and the
explicit quotient of right fractions. -/
def homColimit.typeEquiv :
    (homDiagram W X Y).ColimitType ≃ Hom W X Y where
  toFun := colimitTypeToHom W X Y
  invFun := homToColimitType W X Y
  left_inv := homColimitType_leftInverse W X Y
  right_inv := homColimitType_rightInverse W X Y

/-- The corresponding equivalence from mathlib's abstract Type-valued colimit to explicit
right-fraction classes. -/
noncomputable def homColimit.equiv :
    (colimit (homDiagram W X Y) : Type (max u v)) ≃ Hom W X Y :=
  (Limits.Types.colimitEquivColimitType (homDiagram W X Y)).trans
    (homColimit.typeEquiv W X Y)

/-- The explicit quotient Hom-colimit equivalence sends a coprojection to its right-fraction
class. -/
@[simp]
theorem homColimit.equiv.apply_ι (s : (MorphismProperty.Over W ⊤ X)ᵒᵖ)
    (f : (homDiagram W X Y).obj s) :
    homColimit.equiv W X Y (colimit.ι (homDiagram W X Y) s f) =
      Hom.mk (fraction W X Y s f) := sorry



end Localization
end RightFraction
end MorphismProperty
end CategoryTheory
