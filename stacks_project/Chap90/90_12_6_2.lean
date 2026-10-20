/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.Action
import StacksCheckRecall

/-!
# Action of derivations on the tangent space

A derivation `D : Derivation Λ k k` acts on the tangent space of a predeformation category by
cofibered pushforward along the dual-number automorphism `f_{1,D}`.
-/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

/- 90.12.6.2: the action `a : Derivation Λ k k × T F ⟶ T F` of a `Λ`-derivation of `k` on the
tangent space of a predeformation category, given by `a(D, [x]) = [f_{1,D,*}(x)]`, where
`f_{1,D}` is the automorphism `ArtinianLocalAlgCat.dualNumberAut D` of
`ArtinianLocalAlgCat.dualNumber Λ k` sending `inl r + inr v` to `inl r + inr (v + D r)`. -/
@[stacks 06SW]
#check (CategoryTheory.Functor.derivationAction :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k),
    [CategoryTheory.Functor.IsPredeformationCategory p] →
    Derivation Λ k k → CategoryTheory.Functor.tangentSpace p →
      CategoryTheory.Functor.tangentSpace p)
