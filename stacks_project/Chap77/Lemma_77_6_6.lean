/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap71.Lemma_71_4_6_RelativeAssassin
public import stacks_project.Chap77.Theorem_77_4_7_FlatOver

/-!
# Lemma 77.6.6

If a flat morphism of algebraic spaces over `Y` covers the relative associated
points of a finite-type quasi-coherent module that is flat over `Y`, then the
pullback-pushforward unit is a monomorphism and remains so after any base
change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

namespace relativeAssassin

/-- Lemma 77.6.6 (1): Let `Y` be an algebraic space over a scheme `S`. Let
`g : X' ⟶ X` be a flat morphism of algebraic spaces over `Y` with `X` locally
of finite type over `Y`. Let `F` be a finite type quasi-coherent `𝒪_X`-module
which is flat over `Y`. If `Ass_{X/Y}(F) ⊆ g(|X'|)`, then the canonical map
`F ⟶ g_* g^* F` is injective.
Here `Ass_{X/Y}(F)` is `relativeAssassin f F` with structure map `f : X ⟶ Y`,
`g(|X'|)` is `Set.range (Points.map g)`, the canonical map is
`(pullbackPushforwardAdjunction g).unit.app F`, and injectivity is `Mono` in
`X.Modules`. `F` is flat over `Y` when it is flat over `Y` at every point of
`|X|`. -/
@[stacks 0CW6]
theorem unit_mono_of_subset_range {S : Scheme.{u}} {Y X X' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : X' ⟶ X) [Flat g] [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType]
    (h_flat : ∀ x : Points X, flatOverAt F f x)
    (hAss : relativeAssassin f F ⊆ Set.range (Points.map g)) :
    Mono ((pullbackPushforwardAdjunction g).unit.app F) :=
  sorry

/-- Lemma 77.6.6 (2): Under the hypotheses of `unit_mono_of_subset_range`, the
canonical map remains injective after any base change `h : Z ⟶ Y`.
Here `X_Z` is `Limits.pullback f h`, `F_Z` is
`(pullback (Limits.pullback.fst f h)).obj F`, `g_Z` is
`Limits.pullback.fst (Limits.pullback.fst f h) g`, and the canonical map is
`(pullbackPushforwardAdjunction g_Z).unit.app F_Z`. -/
@[stacks 0CW6]
theorem unit_mono_afterBaseChange_of_subset_range {S : Scheme.{u}}
    {Y X X' : AlgebraicSpace S} (f : X ⟶ Y) (g : X' ⟶ X) [Flat g]
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_flat : ∀ x : Points X, flatOverAt F f x)
    (hAss : relativeAssassin f F ⊆ Set.range (Points.map g))
    {Z : AlgebraicSpace S} (h : Z ⟶ Y) :
    Mono ((pullbackPushforwardAdjunction (Limits.pullback.fst (Limits.pullback.fst f h) g)).unit.app
      ((pullback (Limits.pullback.fst f h)).obj F)) :=
  sorry

end relativeAssassin

end AlgebraicGeometry.AlgebraicSpace.Modules
