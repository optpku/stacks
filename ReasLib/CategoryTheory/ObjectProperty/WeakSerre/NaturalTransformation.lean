/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre.Lattice
public import Mathlib.CategoryTheory.NatIso

/-!
# Isomorphism loci of natural transformations

For a natural transformation between exact functors of abelian categories, the objects where its
component is an isomorphism form a weak Serre class.  This packages the reusable five-lemma
argument independently of any particular comparison map.
-/

@[expose] public section

open CategoryTheory

universe u₁ v₁ u₂ v₂

namespace CategoryTheory.ObjectProperty

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {F G : A ⥤ B}

/-- The object property where a natural transformation has an isomorphism component. -/
def isIsoApp (α : F ⟶ G) : ObjectProperty A :=
  fun X ↦ IsIso (α.app X)

section Abelian

variable [Abelian A] [Abelian B]

/-- The isomorphism-component locus of a natural transformation between exact functors is a weak
Serre class. -/
theorem isIsoApp_isWeakSerreClass (α : F ⟶ G)
    (hF : exactFunctor A B F) (hG : exactFunctor A B G) :
    IsWeakSerreClass (isIsoApp α) := sorry

end Abelian

end CategoryTheory.ObjectProperty
