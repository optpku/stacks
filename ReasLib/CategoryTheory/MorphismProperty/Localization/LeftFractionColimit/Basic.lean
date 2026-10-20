module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Explicit left-fraction Hom-colimit presentation

For a morphism property with a left calculus of fractions, target denominators form a filtered
category.  Equivalence classes of left fractions are the filtered colimit of the corresponding
Hom-sets.

Both directions of the comparison are explicit maps between quotient models.  No inverse function
or colimit witness is selected from an existence theorem; only well-definedness, naturality, and
the inverse laws are proof obligations.
-/

@[expose] public section

universe v u

namespace CategoryTheory
namespace MorphismProperty

open Limits

variable {C : Type u} [Category.{v} C]

/- The existing full subcategory `MorphismProperty.Under W ⊤ Y` owns the target-denominator
category. Thus an object is a denominator
`s : Y ⟶ Y'` with `W s`, while a morphism is an arbitrary map `a : Y' ⟶ Y''`
making the following triangle commute:

```
                   s
       Y ─────────────────▶ Y'
        ╲                   │
       t ╲                  │ a
          ╲                 ▼
           └──────────────▶ Y''
```

In Lean this is `s ≫ a = t`.  The Ore condition produces common successors by
the square

```
                  s₂
       Y ─────────────────▶ Y₂
        │                    │
     s₁ │                    │ t ∈ W
        ▼                    ▼
       Y₁ ─────────────────▶ Y₃
                  a
```

with `s₁ ≫ a = s₂ ≫ t`.  This verifies that the orientation of the
comma-category owner agrees with the source convention for left fractions.

The computational root of the Hom formula below is an equivalence of two
quotients: `homDiagram W X Y` uses `Functor.ColimitType`, while
`LeftFraction.Localization.Hom W X Y` is the quotient by `LeftFractionRel`.
Both directions are therefore explicit quotient maps.  In particular, no
inverse function or `IsColimit` datum is selected from a `sorry`-backed
existence statement.  Only well-definedness, naturality, and inverse laws are
deferred proof fields. -/

namespace LeftFraction

/-- If `W` has a left calculus of fractions, the category `MorphismProperty.Under W ⊤ Y` of denominators
`s : Y ⟶ Y'` in `W` and commutative triangles under `Y` is filtered. -/
@[stacks 05Q0 "filtered category of target denominators"]
instance targetArrows_isFiltered
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] (Y : C) :
    IsFiltered (MorphismProperty.Under W ⊤ Y) := sorry
/- Proof strategy: use `Under.mk ⊤ (𝟙 Y) (W.id_mem Y)` for nonemptiness;
apply `RightFraction.leftFraction` to the span determined by two denominators
to obtain the displayed common successor; then apply
`HasLeftCalculusOfFractions.ext` and `Under.Hom.ext` to equalize parallel
commutative triangles. -/

namespace Localization

/-- The lifted Hom-diagram on target denominators: at
`s : MorphismProperty.Under W ⊤ Y` its value is
`ULift (X ⟶ s.right)`, and a triangle acts by postcomposition.  This abbreviation
deliberately hides the `PUnit`, `Opposite`, and universe transports of the
canonical `Under` and coyoneda owners. -/
abbrev homDiagram (W : MorphismProperty C) (X Y : C) :
    (MorphismProperty.Under W ⊤ Y) ⥤ Type (max u v) :=
  Under.forget W ⊤ Y ⋙ CategoryTheory.Under.forget Y ⋙
    uliftCoyoneda.{u}.obj (Opposite.op X)

/-- The left fraction represented by a diagram element `f` at a denominator
`s : MorphismProperty.Under W ⊤ Y`. Its denominator and membership proof are the direct owner
projections `s.hom` and `s.prop`. -/
def fraction (W : MorphismProperty C) (X Y : C) (s : MorphismProperty.Under W ⊤ Y)
    (f : (homDiagram W X Y).obj s) : W.LeftFraction X Y :=
  LeftFraction.mk (eqToHom (Opposite.unop_op X).symm ≫ f.down) s.hom s.prop

/-- The canonical cocone leg from numerators at `s : MorphismProperty.Under W ⊤ Y` to equivalence
classes of left fractions. -/
def homCoconeApp (W : MorphismProperty C) (X Y : C) (s : MorphismProperty.Under W ⊤ Y) :
    (homDiagram W X Y).obj s → Hom W X Y :=
  fun f ↦ Hom.mk (fraction W X Y s f)

/-- The left-fraction cocone legs respect commutative triangles in
`MorphismProperty.Under W ⊤ Y`. -/
theorem homCocone_naturality (W : MorphismProperty C) (X Y : C)
    {s t : MorphismProperty.Under W ⊤ Y} (a : s ⟶ t) :
    Function.comp (homCoconeApp W X Y t) ((homDiagram W X Y).map a) =
      homCoconeApp W X Y s := sorry
/- Proof strategy: use `Under.w a` for `s.hom ≫ a.right = t.hom` and
`Quot.sound`; the two fractions have common target `t.right`, comparison maps
`a.right` and `𝟙 t.right`, equal numerators by the definition of `homDiagram`,
and target denominator in `W` by `t.prop`. -/

/-- The concrete Type-valued cocone from `homDiagram W X Y` to the quotient of
left fractions. -/
def homCocone (W : MorphismProperty C) (X Y : C) :
    (homDiagram W X Y).CoconeTypes where
  pt := Hom W X Y
  ι := homCoconeApp W X Y
  ι_naturality := homCocone_naturality W X Y

/-- The explicit forward map from the quotient model of the Type-valued colimit
to equivalence classes of left fractions. -/
def colimitTypeToHom (W : MorphismProperty C) (X Y : C) :
    (homDiagram W X Y).ColimitType → Hom W X Y :=
  (homDiagram W X Y).descColimitType (homCocone W X Y)

/-- The concrete Hom-colimit map sends a diagram coprojection to the class of
the left fraction represented by that numerator and denominator. -/
@[simp]
theorem colimitTypeToHom.apply_ιColimitType
    (W : MorphismProperty C) (X Y : C) (s : MorphismProperty.Under W ⊤ Y)
    (f : (homDiagram W X Y).obj s) :
    colimitTypeToHom W X Y ((homDiagram W X Y).ιColimitType s f) =
      Hom.mk (fraction W X Y s f) := sorry

/-- The canonical colimit representative of a left fraction: its index is its
denominator `z.s : Y ⟶ z.Y'`, and its element is its numerator `z.f`. -/
def fractionToColimitType (W : MorphismProperty C) (X Y : C)
    (z : W.LeftFraction X Y) : (homDiagram W X Y).ColimitType :=
  (homDiagram W X Y).ιColimitType (Under.mk ⊤ z.s z.hs)
    (ULift.up (eqToHom (Opposite.unop_op X).symm ≫ z.f))

/-- The concrete Hom-colimit map sends the canonical representative of a left
fraction to its quotient class. -/
@[simp]
theorem colimitTypeToHom.apply_fractionToColimitType
    (W : MorphismProperty C) (X Y : C) (z : W.LeftFraction X Y) :
    colimitTypeToHom W X Y (fractionToColimitType W X Y z) = Hom.mk z := sorry

/-- Related left fractions determine the same canonical colimit representative. -/
theorem fractionToColimitType_eq_of_rel (W : MorphismProperty C) (X Y : C)
    (z₁ z₂ : W.LeftFraction X Y) (h : LeftFractionRel z₁ z₂) :
    fractionToColimitType W X Y z₁ = fractionToColimitType W X Y z₂ := sorry
/- Proof strategy: unpack `h` as a common target `Z` with comparison maps
`t₁` and `t₂`; make the common index with `Under.mk ⊤ (z₁.s ≫ t₁)` and the
membership component of `h`, then apply
`Functor.ιColimitType_eq_of_map_eq_map` to the two induced triangles and use
the numerator equality in `h`. -/

/-- The explicit inverse map from a left-fraction class to the quotient model
of the Hom-colimit.  The `Quot.lift` computation is fixed by
`fractionToColimitType`; only its independence proof is deferred. -/
def homToColimitType (W : MorphismProperty C) (X Y : C) :
    Hom W X Y → (homDiagram W X Y).ColimitType :=
  Quot.lift (fractionToColimitType W X Y) (fractionToColimitType_eq_of_rel W X Y)

/-- The inverse Hom-colimit map sends the class of a left fraction to its explicit
colimit representative. -/
@[simp]
theorem homToColimitType_mk (W : MorphismProperty C) (X Y : C)
    (z : W.LeftFraction X Y) :
    homToColimitType W X Y (Hom.mk z) = fractionToColimitType W X Y z := sorry

/-- `homToColimitType` is a left inverse to `colimitTypeToHom`. -/
theorem homColimitType_leftInverse (W : MorphismProperty C) (X Y : C)
    (x : (homDiagram W X Y).ColimitType) :
    homToColimitType W X Y (colimitTypeToHom W X Y x) = x := sorry
/- Proof strategy: use `Functor.ιColimitType_jointly_surjective` to write `x`
as a diagram coprojection; unfold the two quotient maps, connect the original
index to the reconstructed `Under.mk` index by `Under.homMk (𝟙 s.right)`, and
apply `Functor.ιColimitType_eq_of_map_eq_map` to that comparison. -/

/-- `homToColimitType` is a right inverse to `colimitTypeToHom`. -/
theorem homColimitType_rightInverse (W : MorphismProperty C) (X Y : C)
    (f : Hom W X Y) :
    colimitTypeToHom W X Y (homToColimitType W X Y f) = f := sorry
/- Proof strategy: quotient-induct on `f = Hom.mk z`; the forward map sends the
canonical representative of `z` back to `Hom.mk z`, with the two
`Opposite.unop_op` transports cancelling by category simplification. -/

/-- The data-clean equivalence between the quotient model of the target-denominator
Hom-colimit and the quotient of left fractions.  Its two functions are the
explicit maps above; `sorryAx` can therefore occur only in their quotient
well-definedness, naturality, and inverse-law proofs. -/
def homColimit.typeEquiv (W : MorphismProperty C) (X Y : C) :
    (homDiagram W X Y).ColimitType ≃ Hom W X Y where
  toFun := colimitTypeToHom W X Y
  invFun := homToColimitType W X Y
  left_inv := homColimitType_leftInverse W X Y
  right_inv := homColimitType_rightInverse W X Y

/-- The corresponding equivalence from mathlib's abstract Type-valued colimit
to equivalence classes of left fractions. -/
noncomputable def homColimit.equiv (W : MorphismProperty C) (X Y : C) :
    (colimit (homDiagram W X Y) : Type (max u v)) ≃ Hom W X Y :=
  (Limits.Types.colimitEquivColimitType (homDiagram W X Y)).trans
    (homColimit.typeEquiv W X Y)

/-- The Hom-colimit equivalence sends the coprojection represented by a numerator `f` and
denominator `s` to the corresponding left-fraction class. -/
@[simp]
theorem homColimit.equiv.apply_ι
    (W : MorphismProperty C) (X Y : C) (s : MorphismProperty.Under W ⊤ Y)
    (f : (homDiagram W X Y).obj s) :
    homColimit.equiv W X Y (colimit.ι (homDiagram W X Y) s f) =
      Hom.mk (fraction W X Y s f) := sorry
/- Proof strategy: rewrite the abstract coprojection with
`Limits.Types.colimitEquivColimitType_apply`, unfold `homColimit.typeEquiv` and
`colimitTypeToHom`, and use the defining computation of `Functor.descColimitType` on
`Functor.ιColimitType`. -/

end Localization
end LeftFraction
end MorphismProperty
end CategoryTheory

