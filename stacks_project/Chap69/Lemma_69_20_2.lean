/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap69.«69_3_0_1_HigherDirectImage»
public import stacks_project.Chap69.Definition_69_12_1_Instances

/-!
# Lemma 69.20.2

Every higher direct image of a coherent module along a proper morphism of algebraic
spaces to a locally Noetherian algebraic space is coherent.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- Lemma 69.20.2: if `f : X ⟶ Y` is a proper morphism of algebraic spaces over a scheme
`S` with `Y` locally Noetherian, and `F` is a coherent `𝒪_X`-module, then
`higherDirectImage f F i` is a coherent `𝒪_Y`-module for every `i : ℕ`. -/
@[stacks 08AR]
instance higherDirectImage_isCoherent_of_proper
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
    [IsLocallyNoetherian Y] [Abelian X.Modules] [Abelian Y.Modules]
    [HasInjectiveResolutions X.Modules] (F : X.Modules) [F.IsCoherent]
    (i : ℕ) :
    (higherDirectImage f F i).IsCoherent :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
