module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.MorphismProperty.Localization.RightFraction

/-!
# The right-fraction quotient localization

This module gives the right-oriented quotient model associated to a right calculus of fractions.
Its Hom quotient is directly formed from `RightFractionRel`; composition is implemented through
mathlib's left-fraction quotient for `W.op`, while the public API stays entirely right-oriented.
-/

@[expose] public section

universe v u

namespace CategoryTheory.MorphismProperty.RightFraction

variable {C : Type u} [Category.{v} C]

/-- The category whose objects are those of `C` and whose morphisms are right-fraction classes.

The quotient representation is directly right-oriented. Its composition operation is transported
through mathlib's left-fraction construction on the opposite category. -/
@[nolint unusedArguments]
def Localization (_ : MorphismProperty C) := C

/-- The explicit composite of two right fractions after choosing a common source square.

The compatibility equation says that the numerator of the first fraction and the denominator of
the second fraction agree after the two comparison maps. -/
@[simp]
def comp₀ {W : MorphismProperty C} {X Y Z : C}
    [W.HasRightCalculusOfFractions]
    (z₁ : W.RightFraction X Y) (z₂ : W.RightFraction Y Z)
    (z₃ : W.RightFraction z₁.X' z₂.X') : W.RightFraction X Z :=
  RightFraction.mk (z₃.s ≫ z₁.s) (W.comp_mem _ _ z₃.hs z₁.hs) (z₃.f ≫ z₂.f)

namespace Localization

variable {W : MorphismProperty C} {X Y Z : C}

/-- Morphisms of the right-fraction quotient localization, represented by classes of right
fractions from `X` to `Y`. -/
def Hom (W : MorphismProperty C) (X Y : C) : Type (max u v) :=
  Quot (RightFractionRel : W.RightFraction X Y → W.RightFraction X Y → Prop)

namespace Hom

/-- The right-fraction quotient class represented by a concrete right fraction. -/
def mk (z : W.RightFraction X Y) : Localization.Hom W X Y :=
  Quot.mk _ z

/-- Every morphism of the right-fraction quotient has a right-fraction representative. -/
theorem mk_surjective (f : Localization.Hom W X Y) :
    ∃ z : W.RightFraction X Y, f = mk z := sorry

/-- Two right-fraction representatives define the same quotient morphism exactly when they are
related by the standard right-fraction relation. -/
theorem mk_eq_iff [W.HasRightCalculusOfFractions] (z₁ z₂ : W.RightFraction X Y) :
    mk z₁ = mk z₂ ↔ RightFractionRel z₁ z₂ := sorry

/-- Composition of right-fraction quotient morphisms.

The arguments occur in categorical order: `z₁ : X ⟶ Y` is followed by `z₂ : Y ⟶ Z`.
The implementation reverses their order only internally when using the left-fraction quotient of
`W.op`. -/
@[stacks 04VH "composition on equivalence classes of right fractions"]
noncomputable def comp [W.HasRightCalculusOfFractions]
    (z₁ : Localization.Hom W X Y) (z₂ : Localization.Hom W Y Z) :
    Localization.Hom W X Z :=
  Quot.map
    (fun f : W.op.LeftFraction (Opposite.op Z) (Opposite.op X) ↦ f.unop)
    (fun _ _ h ↦ h.unop)
    (LeftFraction.Localization.Hom.comp
      (Quot.map (fun f : W.RightFraction Y Z ↦ f.op) (fun _ _ h ↦ h.op) z₂)
      (Quot.map (fun f : W.RightFraction X Y ↦ f.op) (fun _ _ h ↦ h.op) z₁))

end Hom

/-- The quotient class of the composite of two explicit right fractions.

The auxiliary right fraction is the canonical right-fraction replacement of the left fraction
with numerator `z₁.f` and denominator `z₂.s`. Consumers should use `comp_eq` when they have a
more convenient explicit common-source square. -/
noncomputable def _root_.CategoryTheory.MorphismProperty.RightFraction.comp
    [W.HasRightCalculusOfFractions]
    (z₁ : W.RightFraction X Y) (z₂ : W.RightFraction Y Z) :
    RightFraction.Localization.Hom W X Z :=
  Hom.mk (RightFraction.comp₀ z₁ z₂
    (LeftFraction.rightFraction (LeftFraction.mk z₁.f z₂.s z₂.hs)))

/-- Any explicit common-source square computes the quotient composite of two right fractions. -/
theorem _root_.CategoryTheory.MorphismProperty.RightFraction.comp_eq
    [W.HasRightCalculusOfFractions]
    (z₁ : W.RightFraction X Y) (z₂ : W.RightFraction Y Z)
    (z₃ : W.RightFraction z₁.X' z₂.X')
    (h₃ : z₃.s ≫ z₁.f = z₃.f ≫ z₂.s) :
    RightFraction.comp z₁ z₂ = Hom.mk (RightFraction.comp₀ z₁ z₂ z₃) := sorry

/-- Quotient composition of representative classes is the named right-fraction composition. -/
theorem Hom.comp_eq [W.HasRightCalculusOfFractions]
    (z₁ : W.RightFraction X Y) (z₂ : W.RightFraction Y Z) :
    Hom.comp (Hom.mk z₁) (Hom.mk z₂) = RightFraction.comp z₁ z₂ := sorry

/-- The category structure on the right-fraction quotient localization. -/
@[stacks 04VH "category structure on the right-fraction localization"]
noncomputable instance instCategory (W : MorphismProperty C)
    [W.HasRightCalculusOfFractions] : Category.{max u v} (RightFraction.Localization W) where
  Hom (X : C) (Y : C) := Hom W X Y
  id (X : C) := Hom.mk (RightFraction.ofHom W (𝟙 X))
  comp f g := Hom.comp f g
  comp_id := sorry
  id_comp := sorry
  assoc := sorry

/-- The quotient localization functor sending a morphism to its identity-denominator right
fraction class. -/
@[simps obj]
noncomputable def Q (W : MorphismProperty C) [W.HasRightCalculusOfFractions] :
    C ⥤ RightFraction.Localization W where
  obj X := X
  map f := Hom.mk (RightFraction.ofHom W f)
  map_id := sorry
  map_comp := sorry

/-- The quotient-localization morphism represented by a right fraction. -/
noncomputable abbrev homMk [W.HasRightCalculusOfFractions]
    (z : W.RightFraction X Y) :
    (Q W).obj X ⟶ (Q W).obj Y :=
  Hom.mk z

/-- The categorical-hom spelling of a right fraction is its quotient class. -/
theorem homMk_eq_hom_mk [W.HasRightCalculusOfFractions]
    (z : W.RightFraction X Y) :
    homMk z = Hom.mk z := sorry

/-- The quotient functor maps an ordinary morphism to its identity-denominator right fraction. -/
theorem Q_map (W : MorphismProperty C) [W.HasRightCalculusOfFractions] (f : X ⟶ Y) :
    (Q W).map f = homMk (RightFraction.ofHom W f) := sorry

/-- Equality of right-fraction quotient morphisms is the standard right-fraction relation. -/
theorem homMk_eq_iff_rightFractionRel [W.HasRightCalculusOfFractions]
    (z₁ z₂ : W.RightFraction X Y) :
    homMk z₁ = homMk z₂ ↔ RightFractionRel z₁ z₂ := sorry

/-- Right-fraction-related representatives induce the same quotient-localization morphism. -/
theorem homMk_eq_of_rightFractionRel [W.HasRightCalculusOfFractions]
    (z₁ z₂ : W.RightFraction X Y) (h : RightFractionRel z₁ z₂) :
    homMk z₁ = homMk z₂ := sorry

/-- An explicit common-source square computes composition of the corresponding localization
morphisms. -/
theorem homMk_comp_homMk [W.HasRightCalculusOfFractions]
    (z₁ : W.RightFraction X Y) (z₂ : W.RightFraction Y Z)
    (z₃ : W.RightFraction z₁.X' z₂.X')
    (h₃ : z₃.s ≫ z₁.f = z₃.f ≫ z₂.s) :
    homMk z₁ ≫ homMk z₂ = homMk (RightFraction.comp₀ z₁ z₂ z₃) := sorry

/-- The right-fraction quotient functor is a localization at `W`. -/
instance instIsLocalization (W : MorphismProperty C) [W.HasRightCalculusOfFractions] :
    (Q W).IsLocalization W := sorry


end Localization

end CategoryTheory.MorphismProperty.RightFraction
