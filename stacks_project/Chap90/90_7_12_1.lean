/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap90.«90_7_12_1_Yoneda»
import StacksCheckRecall

/-!
# Evaluation of morphisms from restricted coyoneda

The named equation of Stacks Tag 06SK: morphisms over `C_Λ` from
`underline R |_{C_Λ}` to a category cofibered in groupoids `F` are equivalent
to objects of the completion fibre `hat F(R)`, by evaluation on identity
truncations.
-/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

/- 90.7.12.1: if `R` is an object of `Ĉ_Λ` and `p : F ⥤ ArtinianLocalAlgCat Λ k`
is cofibered in groupoids, evaluation gives an equivalence from based morphisms
`φ : restrictedCoyoneda R ⟶ p` over `C_Λ` on the identity truncations
`R ⟶ R ⧸ maximalIdeal R ^ (n + 1)` yields `FormalObject.fromRestrictedHom p R`, a functor
`RestrictedHom p R ⥤ Functor.Fiber (Functor.completion p) R` from
`Mor_{C_Λ}(underline R |_{C_Λ}, F)` to `hat F(R)`. -/
@[stacks 06SK]
#check (FormalObject.fromRestrictedHom : ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k)
  [Functor.IsFibered.InGroupoids p.op] (R : CompleteLocalAlgCat Λ k),
  FormalObject.RestrictedHom p R ⥤ Functor.Fiber (Functor.completion p) R)

#check (FormalObject.fromRestrictedHom_isEquivalence :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op]
    (R : CompleteLocalAlgCat Λ k), (FormalObject.fromRestrictedHom p R).IsEquivalence)
