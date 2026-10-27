/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap78.Definition_78_19_1_QuotientSheaf
public import stacks_project.Chap97.«97_10_0_2_Presheaf»
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.SheafHom

/-!
# The relative-Hom fppf sheaf

The functor `Mor_B(Z, X)` is an fppf sheaf on `Sch/S`, and morphisms of sheaves
out of an algebraic space `T` correspond to 05Y1 pairs over `T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat
open StacksProject.Chap97.RelativeHom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

/-- Legacy scheme-test pairs are equivalent to canonical relative-morphism pairs. -/
def HomPair.canonicalEquiv {S : Scheme.{u}} {B : AlgebraicSpace S}
    (Z X : Over B) (U : Over S) : HomPair Z X U ≃ Pair Z.hom X.hom U where
  toFun p := ⟨p.base, p.hom⟩
  invFun p := ⟨p.a, p.b⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

/-- The legacy relative-Hom functor is naturally isomorphic to the canonical presheaf. -/
def functorIsoPresheaf {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B) :
    functor Z X ≅ presheaf Z.hom X.hom :=
  NatIso.ofComponents (fun U ↦ (HomPair.canonicalEquiv Z X U.unop).toIso)
    (by
      intro U V f
      ext p
      rfl)

/-- The relative-Hom functor is an fppf sheaf. -/
theorem functor_isSheaf {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (functor Z X) :=
  (Presheaf.isSheaf_of_iso_iff (functorIsoPresheaf Z X)).mpr (isSheaf Z.hom X.hom)

/-- The relative-Hom sheaf with legacy scheme-test pairs as sections. -/
def homSheaf {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  ⟨functor Z X, functor_isSheaf Z X⟩

/-- Sections of the legacy relative-Hom sheaf are legacy scheme-test pairs. -/
theorem homSheaf_obj {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B)
    (T : Over S) : (homSheaf Z X).obj.obj (op T) = HomPair Z X T := rfl

/-- The legacy and canonical relative-Hom sheaves are canonically isomorphic. -/
def homSheafIso {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B) :
    homSheaf Z X ≅ sheaf Z.hom X.hom :=
  ObjectProperty.isoMk _ (functorIsoPresheaf Z X)

/-- The structure morphism from the legacy relative-Hom sheaf to its base. -/
def toBase {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B) :
    homSheaf Z X ⟶ uliftSheaf B :=
  (homSheafIso Z X).hom ≫ baseMap Z X

/-- The base projection sends a legacy pair to its base morphism under Yoneda. -/
theorem toBase_app {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B)
    (T : (Over S)ᵒᵖ) (p : HomPair Z X T.unop) :
    (toBase Z X).hom.app T p = ULift.up (yonedaEquiv p.base) := by
  change (baseMap Z X).hom.app T (HomPair.canonicalEquiv Z X T.unop p) = _
  exact baseMap_app Z X T _

/-- Pairs over a represented scheme correspond to legacy scheme-test pairs. -/
def overEquiv {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B) (T : Over S) :
    SpacePair Z X (ofOver T) ≃ HomPair Z X T where
  toFun p := ⟨p.base, p.hom⟩
  invFun p := ⟨p.base, p.hom⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

/-- The legacy scheme comparison preserves the base morphism. -/
theorem overEquiv_base {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B)
    {T : Over S} (p : SpacePair Z X (ofOver T)) :
    (overEquiv Z X T p).base = p.base := rfl

/-- The legacy scheme comparison preserves the morphism over the test scheme. -/
theorem overEquiv_hom {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B)
    {T : Over S} (p : SpacePair Z X (ofOver T)) :
    (overEquiv Z X T p).hom = p.hom := rfl

/-- A pair over an algebraic space induces a morphism to the legacy relative-Hom sheaf. -/
def ofPair {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (p : SpacePair Z X T) :
    uliftSheaf T ⟶ homSheaf Z X :=
  SpacePair.toSheafHom p ≫ (homSheafIso Z X).inv

/-- Evaluation of the legacy sheaf morphism restricts the pair to the test scheme. -/
theorem ofPair_hom_app {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (p : SpacePair Z X T) (U : (Over S)ᵒᵖ)
    (x : ULift.{u + 1} (T.functorOfPoints.obj U)) :
    (ofPair p).hom.app U x =
      overEquiv Z X U.unop
        (SpacePair.map (yonedaEquiv.symm x.down : ofOver U.unop ⟶ T) p) := by
  change (HomPair.canonicalEquiv Z X U.unop).symm
    ((SpacePair.toSheafHom p).hom.app U x) = _
  rw [SpacePair.toSheafHom_app]
  rfl

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
