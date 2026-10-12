/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Invertible
public import stacks_project.Chap71.Definition_71_10_9_Regular
public import stacks_project.Chap71.Lemma_71_10_10_Pullback

/-!
# Lemma 71.10.10

A morphism of algebraic spaces for which pullbacks of meromorphic functions are defined
induces a canonical pullback map on meromorphic sections of any module sheaf, and regular
meromorphic sections of invertible sheaves remain regular after pullback.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.isInvertibleObject

noncomputable section

universe u

/-- Lemma 71.10.10 (1)
Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`. Assume that
pullbacks of meromorphic functions are defined for `f`. Let `F` be a sheaf of `𝒪_Y`-modules.
There is a canonical pullback map `f^* : meromorphicSections Y F ⟶ meromorphicSections X ((Modules.pullback f).obj F)`
for meromorphic sections of `F`. -/
@[stacks 0ENC]
def pullbackMeromorphicSections {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [PullbacksMeromorphicFunctionsDefined f] (F : Y.Modules) :
    meromorphicSections Y F → meromorphicSections X ((Modules.pullback f).obj F) :=
  pullbackMeromorphicSectionMap f F

/-- The source-facing pullback of meromorphic sections is the global-sections map assembled
from the étale-square localization cone and `Γ(f_* G) ≅ Γ(G)`. -/
theorem pullbackMeromorphicSections_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [PullbacksMeromorphicFunctionsDefined f] (F : Y.Modules) :
    pullbackMeromorphicSections f F = pullbackMeromorphicSectionMap f F :=
  sorry

/-- Applying `pullbackMeromorphicSections` recovers `pullbackMeromorphicSectionMap`. -/
theorem pullbackMeromorphicSections_apply {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [PullbacksMeromorphicFunctionsDefined f] (F : Y.Modules)
    (s : meromorphicSections Y F) :
    pullbackMeromorphicSections f F s = pullbackMeromorphicSectionMap f F s :=
  sorry

/-- Lemma 71.10.10 (2)
Let `L` be an invertible `𝒪_Y`-module. A regular meromorphic section `s` of `L` pulls back
to a regular meromorphic section of `f^* L`. -/
@[stacks 0ENC]
theorem isRegularMeromorphicSection_pullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [PullbacksMeromorphicFunctionsDefined f] (L : Y.Modules)
    [isInvertibleObject L] {s : meromorphicSections Y L}
    (hs : IsRegularMeromorphicSection Y L s) :
    IsRegularMeromorphicSection X ((Modules.pullback f).obj L)
      (pullbackMeromorphicSections f L s) :=
  sorry
