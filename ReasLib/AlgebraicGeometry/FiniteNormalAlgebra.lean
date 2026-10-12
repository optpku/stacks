/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.Finiteness.Basic
public import ReasLib.RingTheory.Normal.Ring

/-!
# Finite normal algebras over an open subscheme

This file records the algebraic properties used for finite covers of an open
subscheme of an affine spectrum.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace CommAlgCat

/-- The property of an algebra that is finite and normal with etale spectrum over an open. -/
def finiteNormalEtaleOver (A : Type u) [CommRing A]
    (U : (Spec (CommRingCat.of A)).Opens) : ObjectProperty (CommAlgCat.{u} A) :=
  fun B ↦ Module.Finite A B ∧ IsNormalRing B ∧
    Etale (Spec.map (CommRingCat.ofHom (algebraMap A B)) ∣_ U)

/-- Membership in `finiteNormalEtaleOver` exposes its defining conditions. -/
theorem mem_finiteNormalEtaleOver (A : Type u) [CommRing A]
    (U : (Spec (CommRingCat.of A)).Opens) (B : CommAlgCat.{u} A) :
    finiteNormalEtaleOver A U B ↔
      Module.Finite A B ∧ IsNormalRing B ∧
        Etale (Spec.map (CommRingCat.ofHom (algebraMap A B)) ∣_ U) := sorry

/-- The full subcategory of finite normal algebras etale over an open. -/
abbrev FiniteNormalEtaleOver (A : Type u) [CommRing A]
    (U : (Spec (CommRingCat.of A)).Opens) : Type _ :=
  (finiteNormalEtaleOver A U).FullSubcategory

namespace FiniteNormalEtaleOver

/-- Objects in this subcategory are finite over the base. -/
def finite {A : Type u} [CommRing A] {U : (Spec (CommRingCat.of A)).Opens}
    (B : FiniteNormalEtaleOver A U) : Module.Finite A B.obj :=
  B.property.1

/-- Objects in this subcategory have normal underlying rings. -/
def normal {A : Type u} [CommRing A] {U : (Spec (CommRingCat.of A)).Opens}
    (B : FiniteNormalEtaleOver A U) : IsNormalRing B.obj :=
  B.property.2.1

/-- Objects in this subcategory are etale over the specified open. -/
def etale {A : Type u} [CommRing A] {U : (Spec (CommRingCat.of A)).Opens}
    (B : FiniteNormalEtaleOver A U) :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap A B.obj)) ∣_ U) :=
  B.property.2.2

end FiniteNormalEtaleOver

/-- Finite normal algebras etale over an open and torsion-free over the base. -/
def finiteNormalTorsionFreeEtaleOver (A : Type u) [CommRing A]
    (U : (Spec (CommRingCat.of A)).Opens) : ObjectProperty (CommAlgCat.{u} A) :=
  fun B ↦ finiteNormalEtaleOver A U B ∧ Module.IsTorsionFree A B

/-- Membership in the corrected property separates etaleness from torsion-freeness. -/
theorem mem_finiteNormalTorsionFreeEtaleOver (A : Type u) [CommRing A]
    (U : (Spec (CommRingCat.of A)).Opens) (B : CommAlgCat.{u} A) :
    finiteNormalTorsionFreeEtaleOver A U B ↔
      finiteNormalEtaleOver A U B ∧ Module.IsTorsionFree A B := Iff.rfl

/-- The full subcategory of finite normal torsion-free algebras etale over an open. -/
abbrev FiniteNormalTorsionFreeEtaleOver (A : Type u) [CommRing A]
    (U : (Spec (CommRingCat.of A)).Opens) : Type _ :=
  (finiteNormalTorsionFreeEtaleOver A U).FullSubcategory

namespace FiniteNormalTorsionFreeEtaleOver

/-- Objects in this subcategory are finite over the base. -/
def finite {A : Type u} [CommRing A] {U : (Spec (CommRingCat.of A)).Opens}
    (B : FiniteNormalTorsionFreeEtaleOver A U) : Module.Finite A B.obj :=
  B.property.1.1

/-- Objects in this subcategory have normal underlying rings. -/
def normal {A : Type u} [CommRing A] {U : (Spec (CommRingCat.of A)).Opens}
    (B : FiniteNormalTorsionFreeEtaleOver A U) : IsNormalRing B.obj :=
  B.property.1.2.1

/-- Objects in this subcategory are etale over the specified open. -/
def etale {A : Type u} [CommRing A] {U : (Spec (CommRingCat.of A)).Opens}
    (B : FiniteNormalTorsionFreeEtaleOver A U) :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap A B.obj)) ∣_ U) :=
  B.property.1.2.2

/-- Objects in this subcategory are torsion-free over the base. -/
def torsionFree {A : Type u} [CommRing A] {U : (Spec (CommRingCat.of A)).Opens}
    (B : FiniteNormalTorsionFreeEtaleOver A U) : Module.IsTorsionFree A B.obj :=
  B.property.2

end FiniteNormalTorsionFreeEtaleOver

end CommAlgCat
