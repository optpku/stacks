/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap69.«69_3_0_1_HigherDirectImage»
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap75.Lemma_75_7_8_ClosedSupport

/-!
# Lemma 75.7.10

Every higher direct image of a coherent module with support proper over a
locally Noetherian algebraic space, along a locally of finite type morphism of
algebraic spaces, is coherent.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- Lemma 75.7.10: if `f : X ⟶ Y` is a locally of finite type morphism of
algebraic spaces over a scheme `S` with `Y` locally Noetherian, and `F` is a
coherent `𝒪_X`-module whose support is proper over `Y`, then
`higherDirectImage f F p` is a coherent `𝒪_Y`-module for every `p : ℕ`. -/
@[stacks 08GC]
instance higherDirectImage_isCoherent_of_properSupport
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [IsLocallyNoetherian Y] [Abelian X.Modules] [Abelian Y.Modules]
    [HasInjectiveResolutions X.Modules] (F : X.Modules) [F.IsCoherent]
    [ClosedSubset.IsProperOver f (closedSupport F)] (p : ℕ) :
    (higherDirectImage f F p).IsCoherent :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
