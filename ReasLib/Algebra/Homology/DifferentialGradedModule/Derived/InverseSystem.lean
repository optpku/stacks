/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Restriction.Derived
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Opposite
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Pro.Sequential
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fiberwise derived modules on inverse systems of differential graded algebras

For `A : SequentialInverseSystem (CochainDGAlgebra R)`, a derived module system has one derived
right `A n`-module at each stage and a transition after derived extension of scalars.  The
quasi-coherent systems are those whose transition comparisons are isomorphisms.

This auxiliary category localizes each stage before assembling the transitions.  It is useful for
stagewise calculations but is not the global localization `D(ℕ, A)` and does not own the source
notation `QC(A)` outside the explicit `Fiberwise` namespace.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Opposite

namespace DifferentialGradedModule.Derived.Fiberwise

variable {R : Type u} [CommRing R]

/-- A fiberwise derived right-module system over a sequential inverse system of cochain DGAs.
Its map at `n` is the adjoint form of an `A (n + 1)`-linear transition from stage `n + 1` to
stage `n`. -/
structure System (A : SequentialInverseSystem (CochainDGAlgebra.{u, v} R)) where
  /-- The derived right module at stage `n`. -/
  obj (n : ℕ) :
    DifferentialGradedModule.Derived.Category.{u, v} (A.obj (op n))
  /-- The transition comparison after derived extension from `A (n + 1)` to `A n`. -/
  map (n : ℕ) :
    (CochainDGAlgebra.Hom.Derived.extension
      (A.stepMap n)).obj (obj (n + 1)) ⟶ obj n

namespace System

variable {A : SequentialInverseSystem (CochainDGAlgebra.{u, v} R)}

/-- A morphism of derived module systems is a stagewise morphism compatible with every adjacent
transition comparison. -/
structure Hom (M N : System A) where
  /-- The morphism at stage `n`. -/
  app (n : ℕ) : M.obj n ⟶ N.obj n
  /-- Stagewise morphisms commute with the derived extension transition comparisons. -/
  naturality (n : ℕ) :
    (CochainDGAlgebra.Hom.Derived.extension
      (A.stepMap n)).map (app (n + 1)) ≫ N.map n =
        M.map n ≫ app n

namespace Hom

/-- The identity morphism of a derived module system. -/
def id (M : System A) : Hom M M where
  app n := 𝟙 (M.obj n)
  naturality := sorry

/-- Composition of morphisms of derived module systems. -/
def comp {M N P : System A} (g : Hom N P) (f : Hom M N) : Hom M P where
  app n := f.app n ≫ g.app n
  naturality := sorry

/-- Morphisms of derived module systems are determined stagewise. -/
@[ext]
theorem ext {M N : System A} {f g : Hom M N}
    (h : ∀ n : ℕ, f.app n = g.app n) : f = g := sorry

/-- The left identity law for morphisms of derived module systems. -/
theorem id_comp {M N : System A} (f : Hom M N) :
    comp f (id M) = f := sorry

/-- The right identity law for morphisms of derived module systems. -/
theorem comp_id {M N : System A} (f : Hom M N) :
    comp (id N) f = f := sorry

/-- Composition of morphisms of derived module systems is associative. -/
theorem assoc {L M N P : System A}
    (f : Hom L M) (g : Hom M N) (h : Hom N P) :
    comp h (comp g f) = comp (comp h g) f := sorry

end Hom

/-- Derived module systems over a fixed DGA inverse system form a category. -/
instance instCategory : CategoryTheory.Category (System A) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp g f
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- Evaluation of a derived module system at one stage. -/
def eval (A : SequentialInverseSystem (CochainDGAlgebra.{u, v} R)) (n : ℕ) :
    System A ⥤
      DifferentialGradedModule.Derived.Category.{u, v} (A.obj (op n)) where
  obj M := M.obj n
  map f := f.app n
  map_id := sorry
  map_comp := sorry

/-- A derived module system is quasi-coherent when every derived extension transition is an
isomorphism. -/
def quasiCoherent (A : SequentialInverseSystem (CochainDGAlgebra.{u, v} R)) :
    ObjectProperty (System A) :=
  fun M ↦ ∀ n : ℕ, IsIso (M.map n)

/-- Quasi-coherence is exactly invertibility of every adjacent derived extension comparison. -/
theorem quasiCoherent_iff (M : System A) :
    quasiCoherent A M ↔ ∀ n : ℕ, IsIso (M.map n) := sorry

/-- The quasi-coherent derived module systems over `A`. -/
abbrev QC (A : SequentialInverseSystem (CochainDGAlgebra.{u, v} R)) :=
  (quasiCoherent A).FullSubcategory

/-- Every transition comparison of a quasi-coherent module system is an isomorphism. -/
instance qcMapIsIso (M : QC A) (n : ℕ) : IsIso (M.obj.map n) := sorry

end System

/-- A sequential system of left derived `A n`-modules, modeled as right derived modules over
the opposite DGA system. -/
abbrev LeftSystem (A : SequentialInverseSystem (CochainDGAlgebra.{u, v} R)) :=
  System (A ⋙ CochainDGAlgebra.oppositeFunctor R)

/-- The quasi-coherent left derived module systems over `A`, modeled using opposite DGAs. -/
abbrev LeftQC (A : SequentialInverseSystem (CochainDGAlgebra.{u, v} R)) :=
  System.QC (A ⋙ CochainDGAlgebra.oppositeFunctor R)

end DifferentialGradedModule.Derived.Fiberwise
