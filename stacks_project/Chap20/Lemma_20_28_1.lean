/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Adjunction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

namespace AlgebraicGeometry.RingedSpace

/- Lemma 20.28.1
Let f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y) be a morphism of ringed spaces. The functors
L(f)^* : D(𝒪_Y) ⥤ D(𝒪_X) and R(f)_* : D(𝒪_X) ⥤ D(𝒪_Y) are adjoint, equivalently
Hom_{D(𝒪_X)}((L(f)^*).obj 𝒢, ℱ) ≃ Hom_{D(𝒪_Y)}(𝒢, (R(f)_*).obj ℱ) bifunctorially
in ℱ ∈ D(𝒪_X) and 𝒢 ∈ D(𝒪_Y). -/
@[stacks 079W]
#check @modulePullbackDerivedPushforwardAdjunction

#check @Adjunction.homEquiv

end AlgebraicGeometry.RingedSpace
