/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap82.Definition_82_2_5_DeltaDimension
public import stacks_project.Chap82.Lemma_82_7_1_IntegralImage
public import stacks_project.Chap82.Lemma_82_8_2_Pushforward
import StacksCheckRecall

/-!
# Proper pushforward of cycles

In Situation 82.2.1, a proper morphism of good algebraic spaces over `B`
pushes `k`-cycles forward by the residue-weighted integral-image formula on
generators, extended linearly as `Hom.properPushforwardHom`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The `δ`-dimension of the integral image of an integral closed subspace along
a proper morphism over `B` is at most the `δ`-dimension of the source subspace. -/
theorem closedSubspaceDeltaDimension_integralImage_le
    {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX) [IsDecent Y]
    (Z : ClosedSubspace X) [IsIntegral Z.X] :
    pY.closedSubspaceDeltaDimension δ (Z.integralImage f) ≤
      pX.closedSubspaceDeltaDimension δ Z :=
  sorry

/-- Definition 82.8.1 (1): In Situation 82.2.1, for good `X, Y / B` and a proper
morphism `f : X ⟶ Y` over `B`, if `Z ⊂ X` is an integral closed subspace with
`dim_δ(Z) = k` and `Z' = Z.integralImage f` is the integral image of Lemma 82.7.1,
then `f_*[Z]` is `0` when `dim_δ(Z') < k`, and is `deg(Z/Z') [Z']` when
`dim_δ(Z') = k`. Here `[Z]` is the singleton cycle at the image of
`integralGenericPoint Z`, `[Z']` is the singleton at the image of that generic
point along `Z.ι ≫ f`, and `deg(Z/Z')` is `residueDegreeAlong` at that generic
point (Spaces over Fields, Definition 72.5.2, via Lemma 82.7.4). -/
@[stacks 0EP1]
theorem properPushforwardCycle_integralClosedSubspace
    {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX) (k : ℤ) [IsDecent Y]
    (Z : ClosedSubspace X) [IsIntegral Z.X]
    (hZ : pX.closedSubspaceDeltaDimension δ Z = (k : EInt)) :
    let ξ := Points.map Z.ι (ClosedSubspace.integralGenericPoint Z)
    properPushforwardCycle pX pY δ f hf
        (@locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _ ξ 1) =
      if pY.closedSubspaceDeltaDimension δ (Z.integralImage f) < (k : EInt) then
        0
      else
        (residueDegreeAlong pX pY f ξ : ℤ) •
          @locallyFinsuppWithin.single (Points Y) _ ℤ (Classical.decEq _) _
            (Points.map (Z.ι ≫ f) (ClosedSubspace.integralGenericPoint Z)) 1 :=
  sorry

section

variable {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
variable (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX) (k : ℤ)

/- Definition 82.8.1 (2): In Situation 82.2.1, the pushforward of a `k`-cycle
`α = ∑ n_Z [Z]` is the locally finite sum `f_* α = ∑ n_Z f_*[Z]`, encoded as the
additive map `properPushforwardHom pX pY δ f hf k : pX.cycleGroup δ k →+
pY.cycleGroup δ k`. The sum is locally finite by Lemma 82.7.5. -/
@[stacks 0EP1]
#check (properPushforwardHom pX pY δ f hf k :
    pX.cycleGroup δ k →+ pY.cycleGroup δ k)

end

end AlgebraicGeometry.AlgebraicSpace.Hom
