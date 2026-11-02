/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sequential
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Bottom
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
import Mathlib.Tactic.CrossRefAttribute

/-!
# Grothendieck structure on sequential varying-ring modules

@stack 091D

The sheaf-of-modules construction gives the canonical Grothendieck-abelian structure on a
sequential varying-ring module category.  This leaf records the specialization explicitly so
downstream derived-limit declarations can rely on typeclass search without rebuilding a
chapter-local universe pin.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v

namespace CategoryTheory.SequentialInverseSystem

/-- Stacks `091D`: a sequential varying-ring module category is abelian. -/
@[stacks 091D "abelian sequential varying-ring module category"]
noncomputable instance moduleSystemAbelian
    (F : SequentialInverseSystem CommRingCat.{u}) :
    Abelian (ModuleSystem.{u, v} F) :=
  SheafOfModules.Bottom.abelian (bottomRingSheaf F)

/-- Stacks `091D`: sequential varying-ring modules in the universe of the stage rings form a
Grothendieck abelian category relative to that universe. The generator is the coproduct of the
free represented module presheaves, transported through the bottom-topology equivalence. -/
@[stacks 091D "Grothendieck-abelian sequential varying-ring module category"]
noncomputable instance moduleSystemIsGrothendieckAbelian
    (F : SequentialInverseSystem CommRingCat.{u}) :
    IsGrothendieckAbelian.{u} (ModuleSystem.{u, u} F) := by
  let R := ringSystemAsRingCat F
  let G : ℕ → PresheafOfModules.{u} R := fun n ↦
    (PresheafOfModules.free R).obj (uliftYoneda.{u}.obj n)
  have hG : ObjectProperty.IsSeparating (.ofObj G) := by
    intro M N f g h
    ext ⟨n⟩ m
    let e : (G n ⟶ M) ≃ M.obj (op n) :=
      PresheafOfModules.freeHomEquiv.trans uliftYonedaEquiv.{u}
    let e' : (G n ⟶ N) ≃ N.obj (op n) :=
      PresheafOfModules.freeHomEquiv.trans uliftYonedaEquiv.{u}
    obtain ⟨a, rfl⟩ := e.surjective m
    exact congrArg e' (h _ ⟨n⟩ a)
  letI : IsGrothendieckAbelian.{u} (PresheafOfModules.{u} R) :=
    { ab5OfSize := by
        letI : (PresheafOfModules.toPresheaf R).ReflectsIsomorphisms :=
          reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms _
        letI : ReflectsFiniteLimits (PresheafOfModules.toPresheaf R) :=
          reflectsFiniteLimits_of_reflectsIsomorphisms _
        exact ⟨fun J _ _ ↦ HasExactColimitsOfShape.domain_of_functor J
          (PresheafOfModules.toPresheaf R)⟩
      hasSeparator := ⟨∐ G, hG.isSeparator_coproduct⟩ }
  exact IsGrothendieckAbelian.of_equivalence
    (SheafOfModules.Bottom.equivalence (bottomRingSheaf F)).symm

end CategoryTheory.SequentialInverseSystem

end
