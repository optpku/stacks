/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.AutomorphismFunctor
import StacksCheckRecall

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

/- Lemma 90.19.6: if `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids and
satisfies (RS), and `x : F` lies over `A = p.obj x`, then `autFunctor p x :
Under (p.obj x) ⥤ Type` (the automorphism functor Aut(x) : C_A → Sets, after
identifying `Under (p.obj x)` with `A / ArtinianLocalAlgCat Λ k = C_A`) satisfies
(RS): it sends fibre-product squares in `Under (p.obj x)` whose second leg is
surjective to fibre-product squares in `Type`. -/
@[stacks 06JU]
#check (CategoryTheory.Functor.HasRimSchlessinger.autFunctor_isPullback :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.HasRimSchlessinger p] (x : F)
    {W W1 W2 P : Under (p.obj x)}
    (f1 : W1 ⟶ W) (f2 : W2 ⟶ W) (π1 : P ⟶ W1) (π2 : P ⟶ W2)
    (hf2 : Function.Surjective f2.right.hom) (h : IsPullback π1 π2 f1 f2),
    IsPullback ((Functor.autFunctor p x).map π1) ((Functor.autFunctor p x).map π2)
      ((Functor.autFunctor p x).map f1) ((Functor.autFunctor p x).map f2))
