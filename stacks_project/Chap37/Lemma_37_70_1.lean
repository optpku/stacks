/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

/- Lemma 37.70.1: for a locally finite type morphism `f : X ⟶ S`, an object
`E : Scheme.DerivedQCoh X` is relatively `m`-pseudo-coherent over `S` if and only if
all its derived pullbacks along an fppf cover of `X` are relatively
`m`-pseudo-coherent over `S`. -/
@[stacks 0CSN] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver.iff_fppfCover :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.LocallyOfFiniteType f]
      (𝒰 : AlgebraicGeometry.FppfCover.{u, v} X)
      (E : AlgebraicGeometry.Scheme.DerivedQCoh X) (m : ℤ),
      AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver f E.obj m ↔
        ∀ i : 𝒰.I₀,
          @AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver
            _ _ (𝒰.f i ≫ f)
            (AlgebraicGeometry.FppfCover.locallyOfFiniteType_comp f 𝒰 i)
            ((AlgebraicGeometry.Scheme.DerivedQCoh.pullback (𝒰.f i)).obj E).obj m)
