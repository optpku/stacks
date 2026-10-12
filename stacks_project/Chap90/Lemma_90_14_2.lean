/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_10_1_Schlessinger
public import stacks_project.Chap90.Definition_90_27_1_MinimalVersal
public import stacks_project.Chap90.Lemma_90_14_2_Pushforward

/-!
# Lemma 90.14.2

If `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids and has (S1),
and `ξ` is a versal formal object of `p`, then there exists a morphism of
formal objects into `ξ` lying over a subring inclusion with the two minimality
properties of smallest descent.
-/

@[expose] public section

open CategoryTheory
open Functor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace FormalObject

/-- Lemma 90.14.2: if `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids
and has (S1), and `ξ` is a versal formal object of `p`, then there exists a
morphism `f : ξ' ⟶ ξ` of formal objects lying over a subring inclusion such that
every test map `ξ.base ⟶ inclusion.obj A` pushes the corresponding square to a
minimal object of `S_x`, and every morphism of formal objects into `ξ'` is
surjective on complete local bases. -/
@[stacks 06T2]
theorem exists_isSmallestDescent [IsFibered.InGroupoids p.op]
    [HasSchlessingerS1 p] (ξ : FormalObject p) [IsVersal ξ] :
    ∃ (ξ' : FormalObject p) (f : ξ' ⟶ ξ), Hom.IsSmallestDescent f :=
  sorry

end FormalObject
