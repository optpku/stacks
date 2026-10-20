module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InvertiblePullback
public import stacks_project.Chap71.Lemma_71_10_7
public import stacks_project.Chap71.Lemma_71_10_10
public import stacks_project.Chap82.Definition_82_18_1_ChernCap
public import stacks_project.Chap82.Lemma_82_8_2_Pushforward
public import stacks_project.Chap82.Lemma_82_19_3_Degree

/-!
# Proper pushforward of meromorphic-section divisors on algebraic spaces

In Situation 82.2.1, a dominant proper morphism of good integral algebraic
spaces of equal `δ`-dimension pushes `div_{f^* L}(f^* s)` to the
function-field degree times `div_L(s)`, and likewise for first Chern classes
capped with the fundamental cycle.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open Function

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- Pullbacks of meromorphic functions along a dominant morphism of integral
algebraic spaces are defined. -/
instance instPullbacksMeromorphicFunctionsDefined_of_dominant
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [Dominant f] :
    PullbacksMeromorphicFunctionsDefined f :=
  sorry

/-- Pullback of an invertible module along a morphism of algebraic spaces remains
invertible. -/
instance instIsInvertibleObject_pullback {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (L : Y.Modules)
    [isInvertibleObject L] :
    isInvertibleObject ((Modules.pullback f).obj L) :=
  Modules.isInvertibleObject_pullback f L

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
variable [UniversallyCatenary B] [IsQuasiSeparated B]
variable (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable [IsIntegral X]

/-- The divisor cycle of a regular meromorphic section on a good integral space
of `δ`-dimension `n` is an `(n - 1)`-cycle. -/
theorem meromorphicSectionDivisorCycle_mem_of_deltaDimension
    {L : X.Modules} [isInvertibleObject L] (n : ℤ)
    (hX : deltaDimension pX δ (univIrreducibleClosed X) = n)
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s) :
    meromorphicSectionDivisorCycle pX δ s hs ∈ cycleGroup pX δ (n - 1) :=
  sorry

/-- The weight-1 generic-point cycle of a good integral space of `δ`-dimension
`n` is an `(n - 1 + 1)`-cycle, matching the source grade of `firstChernClassCap`. -/
theorem integralSingleton_mem_cycleGroup (n : ℤ)
    (hX : deltaDimension pX δ (univIrreducibleClosed X) = n) :
    @locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _
        (genericPoint_of_good pX (univIrreducibleClosed X)) (1 : ℤ) ∈
      cycleGroup pX δ (n - 1 + 1) :=
  sorry

/-- Lemma 82.19.3 (1): In Situation 82.2.1 let `X`, `Y / B` be good. Let
`f : X ⟶ Y` be a proper morphism. Let `L` be an invertible sheaf on `Y`.
Assume `X`, `Y` integral, `f` dominant, and `dim_δ(X) = dim_δ(Y)`. Let `s`
be a nonzero meromorphic section of `L`. Then
`f_* (div_{f^* L}(f^* s)) = [R(X) : R(Y)] • div_L(s)` as cycles on `Y`. -/
@[stacks 0EQS]
theorem properPushforward_meromorphicSectionDivisor {Y : AlgebraicSpace S}
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    [IsIntegral Y] (f : X ⟶ Y) [Proper f] [Dominant f] (hf : f ≫ pY = pX)
    (n : ℤ) (hX : deltaDimension pX δ (univIrreducibleClosed X) = n)
    (hY : deltaDimension pY δ (univIrreducibleClosed Y) = n)
    (L : Y.Modules) [isInvertibleObject L]
    (s : meromorphicSections Y L) (hs : IsRegularMeromorphicSection Y L s) :
    properPushforwardHom pX pY δ f hf (n - 1)
        ⟨meromorphicSectionDivisorCycle pX δ (pullbackMeromorphicSections f L s)
          (isRegularMeromorphicSection_pullback f L hs),
          meromorphicSectionDivisorCycle_mem_of_deltaDimension pX δ n hX
            (pullbackMeromorphicSections f L s)
            (isRegularMeromorphicSection_pullback f L hs)⟩ =
      (inducedFunctionFieldDegree f : ℤ) •
        ⟨meromorphicSectionDivisorCycle pY δ s hs,
          meromorphicSectionDivisorCycle_mem_of_deltaDimension pY δ n hY s hs⟩ :=
  sorry

/-- Lemma 82.19.3 (2): In the situation of Lemma 82.19.3 (1),
`f_* (c1(f^* L) ∩ [X]) = c1(L) ∩ f_*[X]` in `CH_{n-1}(Y)`. The printed
source formula `c1(L) ∩ f_*[Y]` is this identity, using
`f_*[X] = [R(X) : R(Y)] • [Y]`. -/
@[stacks 0EQS]
theorem properPushforward_firstChernCap_fundamental {Y : AlgebraicSpace S}
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    [IsIntegral Y] (f : X ⟶ Y) [Proper f] [Dominant f] (hf : f ≫ pY = pX)
    (n : ℤ) (hX : deltaDimension pX δ (univIrreducibleClosed X) = n)
    (hY : deltaDimension pY δ (univIrreducibleClosed Y) = n)
    (L : Y.Modules) [isInvertibleObject L]
    (s : meromorphicSections Y L) (hs : IsRegularMeromorphicSection Y L s) :
    chowMk pY δ (n - 1)
        (properPushforwardHom pX pY δ f hf (n - 1)
          ⟨meromorphicSectionDivisorCycle pX δ (pullbackMeromorphicSections f L s)
            (isRegularMeromorphicSection_pullback f L hs),
            meromorphicSectionDivisorCycle_mem_of_deltaDimension pX δ n hX
              (pullbackMeromorphicSections f L s)
              (isRegularMeromorphicSection_pullback f L hs)⟩) =
      firstChernClassCap pY δ L (n - 1)
        (properPushforwardHom pX pY δ f hf (n - 1 + 1)
          ⟨@locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _
              (genericPoint_of_good pX (univIrreducibleClosed X)) (1 : ℤ),
            integralSingleton_mem_cycleGroup pX δ n hX⟩) :=
  sorry

/-- Proper pushforward of the generic-point cycle of `X` is the function-field
degree times the generic-point cycle of `Y`. -/
theorem properPushforward_integralSingleton {Y : AlgebraicSpace S}
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    [IsIntegral Y] (f : X ⟶ Y) [Proper f] [Dominant f] (hf : f ≫ pY = pX)
    (n : ℤ) (hX : deltaDimension pX δ (univIrreducibleClosed X) = n)
    (hY : deltaDimension pY δ (univIrreducibleClosed Y) = n) :
    properPushforwardCycle pX pY δ f hf
        (@locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _
          (genericPoint_of_good pX (univIrreducibleClosed X)) (1 : ℤ)) =
      (inducedFunctionFieldDegree f : ℤ) •
        @locallyFinsuppWithin.single (Points Y) _ ℤ (Classical.decEq _) _
          (genericPoint_of_good pY (univIrreducibleClosed Y)) (1 : ℤ) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
