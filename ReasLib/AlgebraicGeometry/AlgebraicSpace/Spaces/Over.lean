module

public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProper

/-!
# Finite-type and fp-flat-proper groupoids over an algebraic space

The groupoid of finite-type morphisms of algebraic spaces into a fixed algebraic
space `T`, and the analogous groupoid of finite-presentation, flat, and proper
morphisms into `T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces

/-- Objects of `Over T` whose structure morphism is of finite type. -/
def finiteTypeOver {S : Scheme.{u}} (T : AlgebraicSpace S) :
    ObjectProperty (Over T) :=
  fun X ↦ FiniteType X.hom

/-- Membership in `finiteTypeOver T` is finite type of the structure morphism. -/
theorem finiteTypeOver_iff {S : Scheme.{u}} {T : AlgebraicSpace S} (X : Over T) :
    finiteTypeOver T X ↔ FiniteType X.hom := sorry

/-- The groupoid of finite-type morphisms of algebraic spaces into `T`. Morphisms
are isomorphisms of algebraic spaces over `T`. -/
abbrev FtOver {S : Scheme.{u}} (T : AlgebraicSpace S) :=
  Core ((finiteTypeOver T).FullSubcategory)

namespace FtOver

/-- A finite-type morphism `f : X ⟶ T` is a `finiteTypeOver` object. -/
theorem finiteTypeOver_mk {S : Scheme.{u}} {T X : AlgebraicSpace S}
    (f : X ⟶ T) [FiniteType f] : finiteTypeOver T (Over.mk f) := sorry

/-- Package a finite-type morphism `X ⟶ T` as an object of `FtOver T`. -/
def mk {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T) [FiniteType f] :
    FtOver T :=
  ⟨⟨Over.mk f, finiteTypeOver_mk f⟩⟩

/-- The structure morphism of `mk f` is `f`. -/
theorem mk_hom {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FiniteType f] : (mk f).of.obj.hom = f := sorry

/-- An object of `FtOver T` has finite-type structure morphism. -/
theorem spec {S : Scheme.{u}} {T : AlgebraicSpace S} (P : FtOver T) :
    FiniteType P.of.obj.hom := sorry

/-- The structure morphism of an object of `FtOver T` is of finite type. -/
instance finiteType_hom {S : Scheme.{u}} {T : AlgebraicSpace S} (P : FtOver T) :
    FiniteType P.of.obj.hom :=
  P.of.property

/-- The underlying morphism of algebraic spaces of a morphism in `FtOver T`. -/
def homLeft {S : Scheme.{u}} {T : AlgebraicSpace S} {P Q : FtOver T} (α : P ⟶ Q) :
    P.of.obj.left ⟶ Q.of.obj.left :=
  α.iso.hom.hom.left

/-- A morphism in `FtOver T` is a triangle over `T`. -/
theorem homLeft_w {S : Scheme.{u}} {T : AlgebraicSpace S} {P Q : FtOver T}
    (α : P ⟶ Q) : homLeft α ≫ Q.of.obj.hom = P.of.obj.hom := sorry

end FtOver

/-- Objects of `Over T` whose structure morphism is of finite presentation, flat,
and proper. -/
def fpFlatProperOver {S : Scheme.{u}} (T : AlgebraicSpace S) :
    ObjectProperty (Over T) :=
  fun X ↦ FpFlatProper X.hom

/-- Membership in `fpFlatProperOver T` is `FpFlatProper` of the structure
morphism. -/
theorem fpFlatProperOver_iff {S : Scheme.{u}} {T : AlgebraicSpace S}
    (X : Over T) : fpFlatProperOver T X ↔ FpFlatProper X.hom := sorry

/-- The groupoid of finite-presentation, flat, and proper morphisms of algebraic
spaces into `T`. Morphisms are isomorphisms of algebraic spaces over `T`. -/
abbrev FpFlatProperOver {S : Scheme.{u}} (T : AlgebraicSpace S) :=
  Core ((fpFlatProperOver T).FullSubcategory)

namespace FpFlatProperOver

/-- An `FpFlatProper` morphism `f : X ⟶ T` is an `fpFlatProperOver` object. -/
theorem fpFlatProperOver_mk {S : Scheme.{u}} {T X : AlgebraicSpace S}
    (f : X ⟶ T) [FpFlatProper f] : fpFlatProperOver T (Over.mk f) := sorry

/-- Package an `FpFlatProper` morphism `X ⟶ T` as an object of
`FpFlatProperOver T`. -/
def mk {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T) [FpFlatProper f] :
    FpFlatProperOver T :=
  ⟨⟨Over.mk f, fpFlatProperOver_mk f⟩⟩

/-- The structure morphism of `mk f` is `f`. -/
theorem mk_hom {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FpFlatProper f] : (mk f).of.obj.hom = f := sorry

/-- An object of `FpFlatProperOver T` has `FpFlatProper` structure morphism. -/
theorem spec {S : Scheme.{u}} {T : AlgebraicSpace S} (P : FpFlatProperOver T) :
    FpFlatProper P.of.obj.hom := sorry

/-- The structure morphism of an object of `FpFlatProperOver T` is of finite
presentation, flat, and proper. -/
instance fpFlatProper_hom {S : Scheme.{u}} {T : AlgebraicSpace S}
    (P : FpFlatProperOver T) : FpFlatProper P.of.obj.hom :=
  P.of.property

/-- The underlying morphism of algebraic spaces of a morphism in
`FpFlatProperOver T`. -/
def homLeft {S : Scheme.{u}} {T : AlgebraicSpace S} {P Q : FpFlatProperOver T}
    (α : P ⟶ Q) : P.of.obj.left ⟶ Q.of.obj.left :=
  α.iso.hom.hom.left

/-- A morphism in `FpFlatProperOver T` is a triangle over `T`. -/
theorem homLeft_w {S : Scheme.{u}} {T : AlgebraicSpace S}
    {P Q : FpFlatProperOver T} (α : P ⟶ Q) :
    homLeft α ≫ Q.of.obj.hom = P.of.obj.hom := sorry

end FpFlatProperOver

end AlgebraicGeometry.AlgebraicSpace.Spaces
