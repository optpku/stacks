/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.QuasiCompact.Sheaf

/-!
# Finite coproducts of quasi-compact sheaves

This file owns the coproduct-local-surjectivity and finite-coproduct closure
API for quasi-compact set-valued sheaves.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

universe u v

namespace CategoryTheory.Sheaf.LocalSurjectivity

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A finite coproduct of componentwise locally surjective maps of sheaves is locally
surjective. -/
theorem sigmaDesc_of_componentwise
    {α : Type*} [Finite α]
    (Y F : α → Sheaf J (Type (max u v))) [HasCoproduct Y] [HasCoproduct F]
    (γ : ∀ a, Y a ⟶ F a)
    (hγ : ∀ a, IsLocallySurjective (γ a)) :
    IsLocallySurjective (Limits.Sigma.desc fun a ↦ γ a ≫ Limits.Sigma.ι F a) := sorry

/-- Local surjectivity of a coproduct map of sheaves is equivalent to local surjectivity
of its underlying presheaf coproduct map. -/
theorem sigmaDesc_iff_presheaf
    {ι : Type (max u v)} (X : ι → Sheaf J (Type (max u v)))
    {G : Sheaf J (Type (max u v))}
    (α : ∀ i, X i ⟶ G) [HasCoproduct X] :
    IsLocallySurjective (Limits.Sigma.desc α) ↔
      Presheaf.IsLocallySurjective J (Limits.Sigma.desc fun i ↦ (α i).hom) := sorry

/-- Pulling back every summand of a locally surjective coproduct map preserves local
surjectivity of the resulting coproduct map. -/
theorem sigmaDesc_pullbackSnd
    {F G : Sheaf J (Type (max u v))} (q : F ⟶ G)
    {ι : Type (max u v)} (X : ι → Sheaf J (Type (max u v)))
    (α : ∀ i, X i ⟶ G)
    [HasCoproduct X] [HasCoproduct fun i ↦ pullback (α i) q]
    (hα : IsLocallySurjective (Limits.Sigma.desc α)) :
    IsLocallySurjective (Limits.Sigma.desc fun i ↦ pullback.snd (α i) q) := sorry

/-- The coproduct local-surjectivity comparison for an index type small relative to the
ambient sheaf universe. -/
theorem sigmaDesc_iff_presheaf_of_small.{wι}
    {ι : Type wι} [Small.{max u v} ι] (X : ι → Sheaf J (Type (max u v)))
    {G : Sheaf J (Type (max u v))}
    (α : ∀ i, X i ⟶ G) [HasCoproduct X]
    [HasCoproduct fun i ↦ (X i).obj] :
    IsLocallySurjective (Limits.Sigma.desc α) ↔
      Presheaf.IsLocallySurjective J (Limits.Sigma.desc fun i ↦ (α i).hom) := sorry

end CategoryTheory.Sheaf.LocalSurjectivity

namespace CategoryTheory.Sheaf.IsQuasiCompactObject

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} [HasWeakSheafify J (Type (max u v))]

/-- Quasi-compact sheaf objects are stable under isomorphism. -/
instance isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (IsQuasiCompactObject : ObjectProperty (Sheaf J (Type (max u v)))) := sorry

/-- A finite coproduct of quasi-compact sheaves is quasi-compact. -/
theorem finiteCoproduct
    {α : Type*} [Finite α] (F : α → Sheaf J (Type (max u v))) [HasCoproduct F]
    (hF : ∀ a, IsQuasiCompactObject (F a)) :
    IsQuasiCompactObject (∐ F) := sorry

/-- Lemma 7.17.6 (0GMQ): quasi-compact sheaf objects are closed under finite coproducts. -/
@[stacks 0GMQ]
instance isClosedUnderFiniteCoproducts :
    ObjectProperty.IsClosedUnderFiniteCoproducts
      (IsQuasiCompactObject : ObjectProperty (Sheaf J (Type (max u v)))) := sorry

end CategoryTheory.Sheaf.IsQuasiCompactObject
