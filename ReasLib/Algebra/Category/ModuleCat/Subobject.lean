/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Abelian.Images
public import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Explicit ModuleCat Subobjects

Small bridges between a submodule and its canonical categorical subobject presentation.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace ModuleCat

variable {R : Type u} [Ring R]

/-- The canonical categorical complete lattice of module subobjects, with the size universe
fixed to the module carrier universe so that instance inference can find it. -/
@[instance 100, stacks 012J "complete lattice of ModuleCat subobjects"]
noncomputable instance subobjectCompleteLattice (M : ModuleCat.{v} R) :
    CompleteLattice (Subobject M) :=
  Subobject.instCompleteLattice.{v}

/-- The inverse of `subobjectModule` sends a submodule to the subobject represented by its
subtype inclusion. -/
theorem subobjectModule_symm_eq_mk (M : ModuleCat R) (S : Submodule R M) :
    (subobjectModule M).symm S = Subobject.mk (ofHom S.subtype) := by
  apply (subobjectModule M).injective
  simp [subobjectModule]

namespace SubobjectModule

/-- The underlying object of the categorical subobject represented by a submodule is canonically
the module carried by that submodule. -/
@[stacks 012J "underlying object of a submodule subobject"]
noncomputable def underlyingIso (M : ModuleCat R) (S : Submodule R M) :
    Subobject.underlying.obj ((subobjectModule M).symm S) ≅ of R S :=
  (eqToIso <| congrArg (fun T : Subobject M => (T : ModuleCat R))
    (subobjectModule_symm_eq_mk M S)).trans <|
    @Subobject.underlyingIso _ _ _ _ (ofHom S.subtype)
      (ModuleCat.mono_as_hom'_subtype (X := M) S)

end SubobjectModule

end ModuleCat
