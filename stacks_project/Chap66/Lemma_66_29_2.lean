/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_29_2_Pullback

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 66.29.2: let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S`. The pullback functor `f* : Mod(𝒪_Y) ⟶ Mod(𝒪_X)` preserves quasi-coherent sheaves. -/
@[stacks 03GA]
instance pullback_isQuasicoherent {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (F : Y.Modules) [F.IsQuasicoherent] :
    ((pullback f).obj F).IsQuasicoherent :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
