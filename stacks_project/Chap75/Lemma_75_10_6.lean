/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_16_5_Pullback
public import stacks_project.Chap75.Lemma_75_10_6_Comparison
public import stacks_project.Chap75.Lemma_75_10_6_LowerShriek
public import stacks_project.Chap75.Lemma_75_3_1_Restrict

/-!
# Restriction of derived étale lower shriek

Lemma 75.10.6 identifies restriction of `j_! E` along an étale morphism `V ⟶ X` with
lower shriek of the restricted complex along the projection `W ⟶ V` of `W = V ×_X U`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {U X V : AlgebraicSpace S}
variable (j : U ⟶ X) [Etale j] (v : V ⟶ X) [Etale v]
variable [Abelian U.Modules] [Abelian X.Modules] [Abelian V.Modules]
variable [Abelian (Limits.pullback v j).Modules]
variable [(lowerShriek j).Additive] [(restrictFunctor v).Additive]
variable [(restrictFunctor (Limits.pullback.snd v j)).Additive]
variable [(lowerShriek (Limits.pullback.fst v j)).Additive]
variable [PreservesFiniteLimits (lowerShriek j)]
variable [PreservesFiniteColimits (lowerShriek j)]
variable [PreservesFiniteLimits (restrictFunctor v)]
variable [PreservesFiniteColimits (restrictFunctor v)]
variable [PreservesFiniteLimits (restrictFunctor (Limits.pullback.snd v j))]
variable [PreservesFiniteColimits (restrictFunctor (Limits.pullback.snd v j))]
variable [PreservesFiniteLimits (lowerShriek (Limits.pullback.fst v j))]
variable [PreservesFiniteColimits (lowerShriek (Limits.pullback.fst v j))]

/-- Lemma 75.10.6. Let `S` be a scheme. Let `j : U ⟶ X` be an étale morphism of algebraic
spaces over `S`. Given an étale morphism `V ⟶ X` (the official text writes `V ⟶ Y`, a
copy of the clause from Lemma 75.3.1; the fibre product `W = V ×_X U` and the restriction
`|_V` force the morphism `V ⟶ X`), set `W = V ×_X U` and denote `jW : W ⟶ V` the
projection. Then `(j_! E)|_V ≅ jW_!(E|_W)` for `E` in `D(𝒪_U)`. -/
@[stacks 08HA]
noncomputable abbrev restrictLowerShriekIso (E : ModuleDerived U) :
    (restrictFunctorDerived v).obj ((lowerShriekDerived j).obj E) ≅
      (lowerShriekDerived (Limits.pullback.fst v j)).obj
        ((restrictFunctorDerived (Limits.pullback.snd v j)).obj E) :=
  derivedLowerShriekEtaleBaseChangeIso (IsPullback.of_hasPullback v j).flip E

/-- The forward map of `restrictLowerShriekIso` is the derived lower-shriek comparison
morphism of the flipped canonical pullback square. -/
theorem restrictLowerShriekIso_hom (E : ModuleDerived U) :
    (restrictLowerShriekIso j v E).hom =
      derivedLowerShriekEtaleBaseChangeHom (IsPullback.of_hasPullback v j).flip E :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules
