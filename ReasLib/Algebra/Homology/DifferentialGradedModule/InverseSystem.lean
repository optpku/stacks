/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Restriction
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Opposite
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Pro.Sequential
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Opposite
public import ReasLib.CategoryTheory.InverseSystem.Sequential
import Mathlib.Tactic.CrossRefAttribute

/-!
# Differential graded modules on inverse systems of algebras

For `A : SequentialInverseSystem (CochainDGAlgebra R)`, this file owns the ordinary category of right differential
graded module systems over `A`.  A transition from stage `n + 1` to stage `n` is expressed over
`A (n + 1)` by restricting the stage-`n` module along `A (n + 1) ⟶ A n`.

This is the global diagram category which is localized when forming `D(ℕ, A)`.  It is distinct
from a category obtained by first localizing the module category at each stage.
-/

@[expose] public section

noncomputable section

universe u x v

open CategoryTheory Opposite

namespace DifferentialGradedModule.InverseSystem

variable {R : Type u} [CommRing R]

/-- A right differential graded module system over an inverse system of cochain DGAs. -/
@[stacks 0GZG "differential graded modules on an inverse system of DGAs"]
structure System (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) where
  /-- The differential graded `A n`-module at stage `n`. -/
  obj (n : ℕ) : DifferentialGradedModule.{u, v} (A.obj (op n))
  /-- The `A (n + 1)`-linear transition from stage `n + 1` to the restriction of stage `n`. -/
  map (n : ℕ) :
    obj (n + 1) ⟶
      (A.stepMap n).restrictModule (obj n)

namespace System

variable {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}

/-- A morphism of DG-module systems is a stagewise map compatible with every adjacent
transition. -/
structure Hom (M N : System A) where
  /-- The DG-module map at stage `n`. -/
  app (n : ℕ) : M.obj n ⟶ N.obj n
  /-- Compatibility with the transition from stage `n + 1` to stage `n`. -/
  naturality (n : ℕ) :
    M.map n ≫
        (A.stepMap n).restrictHom (app n) =
      app (n + 1) ≫ N.map n

namespace Hom

/-- The identity morphism of a DG-module system. -/
def id (M : System A) : Hom M M where
  app n := 𝟙 (M.obj n)
  naturality := sorry

/-- Composition of morphisms of DG-module systems. -/
def comp {L M N : System A} (g : Hom M N) (f : Hom L M) : Hom L N where
  app n := f.app n ≫ g.app n
  naturality := sorry

/-- Morphisms of DG-module systems are determined by their stage maps. -/
@[ext]
theorem ext {M N : System A} {f g : Hom M N}
    (h : ∀ n : ℕ, f.app n = g.app n) : f = g := sorry

/-- The left identity law for morphisms of DG-module systems. -/
theorem id_comp {M N : System A} (f : Hom M N) :
    comp f (id M) = f := sorry

/-- The right identity law for morphisms of DG-module systems. -/
theorem comp_id {M N : System A} (f : Hom M N) :
    comp (id N) f = f := sorry

/-- Composition of morphisms of DG-module systems is associative. -/
theorem assoc {K L M N : System A}
    (f : Hom K L) (g : Hom L M) (h : Hom M N) :
    comp h (comp g f) = comp (comp h g) f := sorry

end Hom

/-- DG-module systems over a fixed DGA inverse system form a category. -/
instance instCategory : Category (System A) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp g f
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- Evaluation of a DG-module system at one stage. -/
@[stacks 0GZG "stage evaluation of a DG-module inverse system"]
def eval (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (n : ℕ) :
    System A ⥤ DifferentialGradedModule.{u, v} (A.obj (op n)) where
  obj M := M.obj n
  map f := f.app n
  map_id := sorry
  map_comp := sorry

/-- Evaluation recovers the stage object of a DG-module system. -/
@[simp]
theorem eval_obj (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (n : ℕ) (M : System A) :
    (eval A n).obj M = M.obj n := sorry

/-- Evaluation recovers the stage map of a morphism of DG-module systems. -/
@[simp]
theorem eval_map (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (n : ℕ) {M N : System A} (f : M ⟶ N) :
    (eval A n).map f = f.app n := sorry

end System

/-- A left DG-module system over `A`, modeled canonically as a right module system over the
opposite DGA tower. -/
abbrev LeftSystem (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) :=
  System.{u, x, v} (A ⋙ CochainDGAlgebra.oppositeFunctor R)

namespace LeftSystem

/-- Evaluation of a left DG-module system as an actual left module at one stage. -/
@[stacks 0GZI "stage evaluation of a left DG-module inverse system"]
def eval (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (n : ℕ) :
    LeftSystem A ⥤ LeftDifferentialGradedModule.{u, v} (A.obj (op n)) :=
  System.eval (A ⋙ CochainDGAlgebra.oppositeFunctor R) n ⋙
    LeftDifferentialGradedModule.unopFunctor (A.obj (op n))

/-- Left-system evaluation recovers the handedness change of the stage object. -/
@[simp]
theorem eval_obj (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (n : ℕ) (M : LeftSystem A) :
    (eval A n).obj M = LeftDifferentialGradedModule.unop (M.obj n) := sorry

end LeftSystem

end DifferentialGradedModule.InverseSystem
