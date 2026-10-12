/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_10_1_Schlessinger
public import stacks_project.Chap90.Definition_90_27_1_MinimalVersal
public import stacks_project.Chap90.Lemma_90_14_2_Pushforward
public import stacks_project.Chap90.Lemma_90_8_6_PowerSeries

/-!
# Lemma 90.14.3

If `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids and has (S1),
`ξ` is a versal formal object, and `f : ξ' ⟶ ξ` is a smallest descent morphism
as in Lemma 90.14.2, then `f.base` exhibits `ξ.base` as a finite-variable power
series ring over `ξ'.base`, and `ξ'` is versal.
-/

@[expose] public section

open CategoryTheory
open CompleteLocalAlgCat
open Functor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace FormalObject.Hom.IsSmallestDescent

/-- Lemma 90.14.3 (1): if `p` is cofibered in groupoids and has (S1), `ξ` is a
versal formal object, and `f : ξ' ⟶ ξ` is a smallest descent morphism as in
Lemma 90.14.2, then `f.base : ξ'.base ⟶ ξ.base` exhibits `ξ.base` as a
finite-variable power series ring over `ξ'.base`. -/
@[stacks 06T3]
theorem isPowerSeriesOver [IsFibered.InGroupoids p.op] [HasSchlessingerS1 p]
    {ξ ξ' : FormalObject p} [IsVersal ξ] {f : ξ' ⟶ ξ} (hf : Hom.IsSmallestDescent f) :
    IsPowerSeriesOver f.base :=
  sorry

/-- The power series conclusion along the complete local base of a smallest descent
of a versal formal object unpacks to an isomorphism onto a finite-variable cylinder
over the coefficient inclusion. -/
theorem exists_mvPowerSeriesIso [IsFibered.InGroupoids p.op] [HasSchlessingerS1 p]
    {ξ ξ' : FormalObject p} [IsVersal ξ] {f : ξ' ⟶ ξ} (hf : Hom.IsSmallestDescent f) :
    ∃ r : ℕ, ∃ e : ξ.base ≅ ξ'.base.mvPowerSeries r,
      f.base ≫ e.hom = ξ'.base.mvPowerSeriesC r :=
  sorry

/-- Lemma 90.14.3 (2): if `p` is cofibered in groupoids and has (S1), `ξ` is a
versal formal object, and `f : ξ' ⟶ ξ` is a smallest descent morphism as in
Lemma 90.14.2, then `ξ'` is versal. -/
@[stacks 06T3]
def instIsVersal [IsFibered.InGroupoids p.op] [HasSchlessingerS1 p]
    {ξ ξ' : FormalObject p} [IsVersal ξ] {f : ξ' ⟶ ξ} (hf : Hom.IsSmallestDescent f) :
    IsVersal ξ' :=
  sorry

end FormalObject.Hom.IsSmallestDescent
