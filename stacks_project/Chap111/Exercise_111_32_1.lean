/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Types.Morphisms
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopCat TopCat.Presheaf

universe u

variable {X : TopCat.{u}} {ℱ 𝒢 : X.Sheaf (Type u)} (φ : ℱ ⟶ 𝒢)

/- Exercise 111.32.1: a morphism of sheaves of sets on `X` is a monomorphism if and only if each
stalk map `φ_x : ℱ_x → 𝒢_x` is injective. -/
@[stacks 078X] #check (TopCat.Sheaf.mono_iff_stalk_injective φ :
  Mono φ ↔ ∀ x : X, Function.Injective ((stalkFunctor (Type u) x).map φ.hom))
