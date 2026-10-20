module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage.SerreVanishing
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage`
-- pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for definitional equality.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 69.20.1. Higher direct images of a coherent module vanish uniformly in all
positive cohomological degrees after sufficiently large twists by the pulled-back 𝒪(1).
Natural twist degrees describe a cofinal nonnegative tail of the integer degrees in the
source: the eventual bound may be increased to at least zero. -/
@[stacks 08AQ] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.higherDirectImage_projectiveTwist_eventually_isZero :
    ∀ (n : ℕ)
    (i : X ⟶ ProjectiveSpace n Y) [IsClosedImmersion i] [IsNoetherian Y]
    [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
    (F : X.Modules) [F.IsCoherent],
    ∃ d0 : ℕ, ∀ d : ℕ, d0 ≤ d → ∀ p : ℕ, 0 < p →
      IsZero
        (higherDirectImage (i ≫ ProjectiveSpace.toBase n Y)
          (F ⊗ tensorPower ((pullback i).obj (ProjectiveSpace.twistingSheaf n Y)) d) p))

end AlgebraicGeometry.AlgebraicSpace.Modules
