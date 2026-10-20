module

public import Mathlib.CategoryTheory.Core
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Family
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.BaseChange

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

/-- The object property of morphisms `X ⟶ T` of algebraic spaces that are
families of curves. -/
abbrev familyOver {S : Scheme.{u}} (T : AlgebraicSpace S) :
    ObjectProperty (Over T) :=
  fun X ↦ IsFamily X.hom

/-- Membership in `familyOver T` is that the structure morphism is a family of
curves. -/
theorem familyOver_iff {S : Scheme.{u}} {T : AlgebraicSpace S} (X : Over T) :
    familyOver T X ↔ IsFamily X.hom :=
  Iff.rfl

/-- The groupoid of families of curves over an algebraic space `T`: objects are
morphisms `X ⟶ T` of algebraic spaces that are families of curves, and
morphisms are isomorphisms over `T`. -/
abbrev FamilyOver {S : Scheme.{u}} (T : AlgebraicSpace S) :=
  Core ((familyOver T).FullSubcategory)

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
  rfl

/-- The total space of `mk f` is `X`. -/
theorem mk_space {S : Scheme.{u}} {X T : AlgebraicSpace S} (f : X ⟶ T)
    [IsFamily f] : space (mk f) = X :=
  rfl

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
  FamilyOver.mk (Curves.hom P)

/-- The structure morphism of `FamilyOver.ofObj P` is `Curves.hom P`. -/
theorem FamilyOver.ofObj_hom {S : Scheme.{u}} (P : Obj S) :
    FamilyOver.hom (FamilyOver.ofObj P) = Curves.hom P :=
  rfl

/-- Being a family of curves is stable under base change. -/
instance instIsFamily_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y) [IsFamily f] :
    IsFamily (pullback.snd f g) :=
  instIsFamily_of_fpFlatProper_relativeDimensionLE _

/-- The total-space map underlying an isomorphism of families over a fixed base. -/
def FamilyOver.spaceMap {S : Scheme.{u}} {T : AlgebraicSpace S} {P Q : FamilyOver T}
    (φ : P ⟶ Q) : FamilyOver.space P ⟶ FamilyOver.space Q :=
  φ.iso.hom.hom.left

/-- The total-space map is the left component of the underlying morphism over the base. -/
theorem FamilyOver.spaceMap_eq {S : Scheme.{u}} {T : AlgebraicSpace S}
    {P Q : FamilyOver T} (φ : P ⟶ Q) :
    FamilyOver.spaceMap φ = φ.iso.hom.hom.left := rfl

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
