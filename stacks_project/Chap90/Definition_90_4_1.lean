/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Definition 90.4.1: Ĉ_Λ is the category of pairs (R, φ) where R is a Noetherian
complete local Λ-algebra and φ : ResidueField R ≃ₐ[Λ] k is a Λ-algebra isomorphism;
morphisms (S, ψ) ⟶ (R, φ) are local Λ-algebra maps f : S → R satisfying
φ.comp (ResidueField.mapAlgHom f) = ψ. -/
@[stacks 06GW]
#check (CompleteLocalAlgCat Λ k : Type (u + 1))

variable (R S : CompleteLocalAlgCat Λ k)

#check (CompleteLocalAlgCat.Hom R S : Type u)

#check (CompleteLocalAlgCat.category : Category.{u} (CompleteLocalAlgCat Λ k))
