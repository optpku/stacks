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

/- Exercise 111.32.3: a morphism of sheaves of sets on `X` is an epimorphism if and only if each
stalk map `φ_x : ℱ_x → 𝒢_x` is surjective. -/
@[stacks 02EU] #check (TopCat.Sheaf.epi_iff_stalk_surjective φ :
  Epi φ ↔ ∀ x : X, Function.Surjective ((stalkFunctor (Type u) x).map φ.hom))
