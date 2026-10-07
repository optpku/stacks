module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap69.«69_3_0_1_HigherDirectImage»
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap69.Lemma_69_20_1_ProjectiveSpace
public import stacks_project.Chap69.Lemma_69_20_1_Tensor
public import stacks_project.Chap69.Lemma_69_20_1_Twist
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent

/-!
# Lemma 69.20.1

Higher direct images of a coherent module on an algebraic space vanish after twisting
by a sufficiently large power of the pullback of `𝒪(1)` along a closed immersion into
projective space over a Noetherian algebraic space.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- Lemma 69.20.1: let `S` be a scheme. Consider a commutative diagram of algebraic spaces
over `S` with a closed immersion `i : X ⟶ ProjectiveSpace n Y` and structure morphism
`ProjectiveSpace.toBase n Y : ProjectiveSpace n Y ⟶ Y`, and set
`f = i ≫ ProjectiveSpace.toBase n Y`. Assume `i` is a closed immersion and `Y` is
Noetherian. Set `L` to be the pullback of `ProjectiveSpace.twistingSheaf n Y` along `i`.
Let `F` be a coherent module on `X`. Then there exists an integer `d0` such that for all
`d ≥ d0` and all `p > 0` one has
`IsZero (higherDirectImage f (F ⊗ tensorPowerInt L d) p)`. -/
@[stacks 08AQ]
theorem higherDirectImage_projectiveTwist_eventually_isZero
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (n : ℕ)
    (i : X ⟶ ProjectiveSpace n Y) [IsClosedImmersion i] [IsNoetherian Y]
    [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
    (F : X.Modules) [F.IsCoherent] :
    ∃ d0 : ℕ, ∀ d : ℕ, d0 ≤ d → ∀ p : ℕ, 0 < p →
      IsZero
        (higherDirectImage (i ≫ ProjectiveSpace.toBase n Y)
          (F ⊗ tensorPowerInt ((pullback i).obj (ProjectiveSpace.twistingSheaf n Y)) d) p) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
