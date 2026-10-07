module

public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap99.Situation_99_15_1_Category

/-!
# Families of curves over algebraic spaces

A morphism of algebraic spaces is a family of curves when it is of finite
presentation, flat, and proper, of relative dimension at most `1`. The groupoid
of such families over a fixed algebraic space `T` is the core of the full
subcategory of `Over T` on this property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- A morphism of algebraic spaces is a family of curves if it is of finite
presentation, flat, and proper, and has relative dimension at most `1`. -/
@[mk_iff]
class IsFamily {S : Scheme.{u}} {X T : AlgebraicSpace S} (f : X ⟶ T) : Prop
    extends FpFlatProper f, RelativeDimensionLE f 1

/-- An fp-flat-proper morphism of relative dimension at most `1` is a family of
curves. -/
instance instIsFamily_of_fpFlatProper_relativeDimensionLE {S : Scheme.{u}}
    {X T : AlgebraicSpace S} (f : X ⟶ T) [hfp : FpFlatProper f]
    [hd : RelativeDimensionLE f 1] : IsFamily f where
  toFpFlatProper := hfp
  toRelativeDimensionLE := hd

/-- A family of curves is of finite presentation, flat, and proper. -/
instance instFpFlatProper_of_isFamily {S : Scheme.{u}} {X T : AlgebraicSpace S}
    (f : X ⟶ T) [h : IsFamily f] : FpFlatProper f :=
  h.toFpFlatProper

/-- A family of curves has relative dimension at most `1`. -/
instance instRelativeDimensionLE_of_isFamily {S : Scheme.{u}}
    {X T : AlgebraicSpace S} (f : X ⟶ T) [h : IsFamily f] :
    RelativeDimensionLE f 1 :=
  h.toRelativeDimensionLE

namespace IsFamily

/-- A family of curves is fp-flat-proper, of finite presentation, flat, proper,
and of relative dimension at most `1`. -/
theorem spec {S : Scheme.{u}} {X T : AlgebraicSpace S} (f : X ⟶ T) :
    IsFamily f ↔
      FpFlatProper f ∧ FinitePresentation f ∧ Flat f ∧ Proper f ∧
        RelativeDimensionLE f 1 :=
  sorry

end IsFamily

/-- The structure morphism of a scheme-base family of curves is a family of
curves in the sense of algebraic spaces. -/
instance instIsFamily_hom {S : Scheme.{u}} (P : Obj S) : IsFamily (hom P) :=
  sorry

/-- The object property of morphisms `X ⟶ T` of algebraic spaces that are
families of curves. -/
abbrev familyOver {S : Scheme.{u}} (T : AlgebraicSpace S) :
    ObjectProperty (Over T) :=
  fun X ↦ IsFamily X.hom

/-- Membership in `familyOver T` is that the structure morphism is a family of
curves. -/
theorem familyOver_iff {S : Scheme.{u}} {T : AlgebraicSpace S} (X : Over T) :
    familyOver T X ↔ IsFamily X.hom :=
  sorry

/-- The groupoid of families of curves over an algebraic space `T`: objects are
morphisms `X ⟶ T` of algebraic spaces that are families of curves, and
morphisms are isomorphisms over `T`. -/
abbrev FamilyOver {S : Scheme.{u}} (T : AlgebraicSpace S) :=
  Core ((familyOver T).FullSubcategory)

/-- The structure morphism of a scheme-base family of curves. -/
abbrev objHom {S : Scheme.{u}} (P : Obj S) : space P ⟶ ofOver (base P) :=
  hom P

namespace FamilyOver

/-- Package a family of curves `f : X ⟶ T` as an object of `FamilyOver T`. -/
def mk {S : Scheme.{u}} {X T : AlgebraicSpace S} (f : X ⟶ T) [IsFamily f] :
    FamilyOver T where
  of := ⟨Over.mk f, inferInstanceAs (IsFamily f)⟩

/-- The total space of a family of curves over an algebraic space. -/
abbrev space {S : Scheme.{u}} {T : AlgebraicSpace S} (P : FamilyOver T) :
    AlgebraicSpace S :=
  P.of.obj.left

/-- The structure morphism of a family of curves over an algebraic space. -/
abbrev hom {S : Scheme.{u}} {T : AlgebraicSpace S} (P : FamilyOver T) :
    space P ⟶ T :=
  P.of.obj.hom

/-- The structure morphism of `mk f` is `f`. -/
theorem mk_hom {S : Scheme.{u}} {X T : AlgebraicSpace S} (f : X ⟶ T)
    [IsFamily f] : hom (mk f) = f :=
  sorry

/-- The total space of `mk f` is `X`. -/
theorem mk_space {S : Scheme.{u}} {X T : AlgebraicSpace S} (f : X ⟶ T)
    [IsFamily f] : space (mk f) = X :=
  sorry

/-- The structure morphism of a packaged family of curves is a family of
curves. -/
instance instIsFamily_hom {S : Scheme.{u}} {T : AlgebraicSpace S}
    (P : FamilyOver T) : IsFamily (hom P) :=
  P.of.property

end FamilyOver

/-- A scheme-base family of curves, viewed as a family over the algebraic space
associated to its base scheme. -/
def FamilyOver.ofObj {S : Scheme.{u}} (P : Obj S) :
    FamilyOver (ofOver (base P)) :=
  FamilyOver.mk (objHom P)

/-- The structure morphism of `FamilyOver.ofObj P` is `objHom P`. -/
theorem FamilyOver.ofObj_hom {S : Scheme.{u}} (P : Obj S) :
    FamilyOver.hom (FamilyOver.ofObj P) = objHom P :=
  sorry

/-- Finite presentation, flatness, and properness of morphisms of algebraic
spaces are stable under base change. -/
instance instFpFlatProper_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y) [FpFlatProper f] :
    FpFlatProper (pullback.snd f g) :=
  sorry

/-- Relative dimension at most `1` is stable under base change. -/
instance instRelativeDimensionLE_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [RelativeDimensionLE f 1] : RelativeDimensionLE (pullback.snd f g) 1 :=
  sorry

/-- Being a family of curves is stable under base change. -/
instance instIsFamily_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y) [IsFamily f] :
    IsFamily (pullback.snd f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
