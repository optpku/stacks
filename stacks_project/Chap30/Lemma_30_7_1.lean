/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.Pushforward

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.OpenCoverCech

/- Lemma 30.7.1
For a finite affine open cover and affine diagonals, the pushed-forward Čech resolution is
naturally isomorphic in the bounded-below derived category to derived pushforward.
-/
@[stacks 01XL] #check
  (comparison_isIso :
    ∀ {X S : Scheme.{u}} {ι : Type u}
      (f : X ⟶ S)
      [IsAffineHom (pullback.diagonal (terminal.from X))]
      [IsAffineHom (pullback.diagonal (terminal.from S))]
      [Finite ι] (𝒰 : ι → X.Opens) (h𝒰 : IsOpenCover 𝒰)
      (h𝒰_affine : ∀ i, IsAffineOpen (𝒰 i)),
      IsIso (comparison f 𝒰 h𝒰))

#check
  (pushforward_term_isQuasicoherent :
    ∀ {X S : Scheme.{u}} {ι : Type u}
      (f : X ⟶ S)
      [IsAffineHom (pullback.diagonal (terminal.from X))]
      [IsAffineHom (pullback.diagonal (terminal.from S))]
      [Finite ι] (𝒰 : ι → X.Opens) (h𝒰 : IsOpenCover 𝒰)
      (h𝒰_affine : ∀ i, IsAffineOpen (𝒰 i))
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] (p : ℕ),
      ((pushforward f 𝒰 ℱ).X p).IsQuasicoherent)

#check
  (pushforwardInt_isBoundedBelow :
    ∀ {X S : Scheme.{u}} {ι : Type u}
      (f : X ⟶ S) (𝒰 : ι → X.Opens) (ℱ : X.Modules),
      CochainComplex.plus S.Modules
        (pushforwardInt f 𝒰 ℱ))

end AlgebraicGeometry.Scheme.OpenCoverCech
