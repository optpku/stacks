/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Noetherian.Defs
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap69.Lemma_69_16_9

/-!
# Lemma 69.21.1

A cohomological criterion for ampleness of an invertible sheaf on a proper algebraic
space over a Noetherian ring.
-/

@[expose]
public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Modules

/-- An invertible module `L` on an algebraic space `X` is ample on `X` as a scheme when `X`
is a scheme and `toSchemeModule e L` is ample on every representing scheme. -/
def isSchemeAndAmple {S : Scheme.{u}} {X : AlgebraicSpace S} (L : X.Modules) : Prop :=
  IsScheme X ∧ ∀ {T : Over S} (e : X ≅ ofOver T),
    Scheme.Modules.isAmpleObject (toSchemeModule e L)

/-- `isSchemeAndAmple L` unpacks as `IsScheme X` together with ampleness of
`toSchemeModule e L` on every representing isomorphism `e`. -/
theorem isSchemeAndAmple_iff {S : Scheme.{u}} {X : AlgebraicSpace S} (L : X.Modules) :
    isSchemeAndAmple L ↔
      IsScheme X ∧ ∀ {T : Over S} (e : X ≅ ofOver T),
        Scheme.Modules.isAmpleObject (toSchemeModule e L) :=
  sorry

end Modules

/-- Lemma 69.21.1: let `R` be a Noetherian ring, let `X` be a proper algebraic space over
`R`, and let `L` be an invertible `𝒪_X`-module. The following are equivalent: `X` is a
scheme and `L` is ample on `X`; for every coherent `𝒪_X`-module `F` there exists `n₀ ≥ 0`
such that `H^p(X, F ⊗ L^{⊗ n}) = 0` for all `n ≥ n₀` and `p > 0`; and for every coherent
`𝒪_X`-module `F` there exists `n ≥ 1` such that `H¹(X, F ⊗ L^{⊗ n}) = 0`. -/
@[stacks 0GFA]
theorem isSchemeAndAmple_tfae {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : AlgebraicSpace (Spec (CommRingCat.of R))}
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) [Proper f]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    (L : X.Modules) [isInvertibleObject L] :
    List.TFAE
      [ Modules.isSchemeAndAmple L,
        ∀ F : X.Modules, F.IsCoherent →
          ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ p : ℕ, 0 < p →
            IsZero (cohomology X (F ⊗ Modules.tensorPowerInt L n) p),
        ∀ F : X.Modules, F.IsCoherent →
          ∃ n : ℕ, 0 < n ∧
            IsZero (cohomology X (F ⊗ Modules.tensorPowerInt L n) 1) ] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
