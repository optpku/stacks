/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.CharacterModule.TensorHom
public import ReasLib.LinearAlgebra.UniversallyInjective

@[expose] public section

open CategoryTheory

universe u

namespace CharacterModule

/-- A morphism of modules is universally injective if and only if its character-dual map is a
split epimorphism. -/
theorem universallyInjective_iff_isSplitEpi_dualMap
    (R : Type u) [CommRing R] {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    LinearMap.UniversallyInjective.{u, u, u, u} f.hom ↔
      IsSplitEpi (dualMap R f) := sorry

end CharacterModule
