/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import stacks_project.Chap90.Definition_90_16_8_RimSchlessinger
public import stacks_project.Chap90.Definition_90_19_5_AutFunctor

/-!
# Automorphism functors satisfy (RS)

If `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids and satisfies (RS),
then for any `x : F` the automorphism functor `autFunctor p x` on `Under (p.obj x)`
satisfies the Set-valued Rim-Schlessinger condition (Schlessinger's (H4)).
-/

@[expose] public section

open CategoryTheory Limits Under

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- The Rim-Schlessinger condition includes being cofibered in groupoids. -/
instance HasRimSchlessinger.instIsFiberedInGroupoids
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p] :
    IsFibered.InGroupoids p.op :=
  HasRimSchlessinger.isCofiberedInGroupoids

/-- Lemma 90.19.6: if `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids and
satisfies (RS), and `x : F` lies over `A = p.obj x`, then `autFunctor p x :
Under (p.obj x) ⥤ Type` (the automorphism functor Aut(x) : C_A → Sets, after
identifying `Under (p.obj x)` with `A / ArtinianLocalAlgCat Λ k = C_A`) satisfies
(RS): it sends fibre-product squares in `Under (p.obj x)` whose second leg is
surjective to fibre-product squares in `Type`. -/
@[stacks 06JU]
theorem HasRimSchlessinger.autFunctor_isPullback
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p] (x : F)
    {W W1 W2 P : Under (p.obj x)}
    (f1 : W1 ⟶ W) (f2 : W2 ⟶ W) (π1 : P ⟶ W1) (π2 : P ⟶ W2)
    (hf2 : Function.Surjective f2.right.hom) (h : IsPullback π1 π2 f1 f2) :
    IsPullback ((autFunctor p x).map π1) ((autFunctor p x).map π2)
      ((autFunctor p x).map f1) ((autFunctor p x).map f2) := sorry

/-- Images of a fibre-product object under the two projections agree after applying
`autFunctor p x` to the cospan. -/
theorem autFunctorComparison_mem
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op] (x : F)
    {W W1 W2 P : Under (p.obj x)}
    (f1 : W1 ⟶ W) (f2 : W2 ⟶ W) (π1 : P ⟶ W1) (π2 : P ⟶ W2)
    (h : IsPullback π1 π2 f1 f2) (α : (autFunctor p x).obj P) :
    (autFunctor p x).map f1 ((autFunctor p x).map π1 α) =
      (autFunctor p x).map f2 ((autFunctor p x).map π2 α) := sorry

/-- The induced map `(autFunctor p x).obj P → Types.PullbackObj (map f1) (map f2)`
associated to a fibre-product square in `Under (p.obj x)`. -/
noncomputable def autFunctorComparison
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op] (x : F)
    {W W1 W2 P : Under (p.obj x)}
    (f1 : W1 ⟶ W) (f2 : W2 ⟶ W) (π1 : P ⟶ W1) (π2 : P ⟶ W2)
    (h : IsPullback π1 π2 f1 f2) :
    (autFunctor p x).obj P →
      Types.PullbackObj ((autFunctor p x).map f1) ((autFunctor p x).map f2) :=
  fun α ↦ ⟨⟨(autFunctor p x).map π1 α, (autFunctor p x).map π2 α⟩,
    autFunctorComparison_mem p x f1 f2 π1 π2 h α⟩

/-- The automorphism-functor (RS) comparison map sends `α` to the pair
`(map π1 α, map π2 α)`. -/
theorem autFunctorComparison_spec
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op] (x : F)
    {W W1 W2 P : Under (p.obj x)}
    (f1 : W1 ⟶ W) (f2 : W2 ⟶ W) (π1 : P ⟶ W1) (π2 : P ⟶ W2)
    (h : IsPullback π1 π2 f1 f2) (α : (autFunctor p x).obj P) :
    (autFunctorComparison p x f1 f2 π1 π2 h α).1 =
      ((autFunctor p x).map π1 α, (autFunctor p x).map π2 α) := sorry

/-- Under (RS), the automorphism-functor comparison into `Types.PullbackObj` is
bijective along a fibre-product square whose second leg is surjective. -/
theorem HasRimSchlessinger.autFunctorComparison_bijective
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p] (x : F)
    {W W1 W2 P : Under (p.obj x)}
    (f1 : W1 ⟶ W) (f2 : W2 ⟶ W) (π1 : P ⟶ W1) (π2 : P ⟶ W2)
    (h : IsPullback π1 π2 f1 f2) (hf2 : Function.Surjective f2.right.hom) :
    Function.Bijective (autFunctorComparison p x f1 f2 π1 π2 h) := sorry

end CategoryTheory.Functor
