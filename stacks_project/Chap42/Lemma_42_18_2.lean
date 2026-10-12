/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Principal.GraphClosure
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RationalFunctionGraph

/- Lemma 42.18.2 (1): the projection from the closure of the graph of an invertible
section to `X` is proper. -/
@[stacks 02RQ] #check
  (AlgebraicGeometry.RationalFunctionGraph.instIsProperFst :
    ∀ {S : Scheme.{u}} (X : Over S) (U : X.left.Opens) (s : Γ(X.left, U)ˣ),
      IsProper (fst X U s))

/- Lemma 42.18.2 (2): over `U`, the projection from the graph closure restricts to an
isomorphism. -/
@[stacks 02RQ] #check
  (AlgebraicGeometry.RationalFunctionGraph.instIsIsoRestrictFst :
    ∀ {S : Scheme.{u}} (X : Over S) (U : X.left.Opens) (s : Γ(X.left, U)ˣ)
      [UniversallyCatenary S] [LocallyOfFiniteType X.hom] [IsIntegral X.left]
      [Nonempty U], IsIso (fst X U s ∣_ U))

/- Lemma 42.18.2 (3): the inverse image `Y₀ = q⁻¹D₀` is a defined pullback
effective Cartier divisor. -/
@[stacks 02RQ] #check
  (AlgebraicGeometry.RationalFunctionGraph.instIsEffectiveCartierZeroDivisor :
    ∀ {S : Scheme.{u}} (X : Over S) (U : X.left.Opens) (s : Γ(X.left, U)ˣ)
      [IsIntegral X.left] [Nonempty U],
      Scheme.IdealSheafData.pullbackDefined
        (ProjectiveLine.Relative.zeroDivisor S) (snd X U s))

/- Lemma 42.18.2 (4): the inverse image `Y∞ = q⁻¹D∞` is a defined pullback
effective Cartier divisor. -/
@[stacks 02RQ] #check
  (AlgebraicGeometry.RationalFunctionGraph.instIsEffectiveCartierInfinityDivisor :
    ∀ {S : Scheme.{u}} (X : Over S) (U : X.left.Opens) (s : Γ(X.left, U)ˣ)
      [IsIntegral X.left] [Nonempty U],
      Scheme.IdealSheafData.pullbackDefined
        (ProjectiveLine.Relative.infinityDivisor S) (snd X U s))

/- Lemma 42.18.2 (5): on the graph closure, the principal divisor of `f` is the
degree-`n - 1` cycle of `Y₀` minus that of `Y∞`. -/
@[stacks 02RQ] #check
  (AlgebraicGeometry.RationalFunctionGraph.principal_eq_zero_sub_infinity :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
      [IsDimensionFunction delta] (X : Over S) [LocallyOfFiniteType X.hom]
      [IsIntegral X.left] (n : ℤ) (f : X.left.functionFieldˣ)
      (U : X.left.Opens) [Nonempty U] (s : Γ(X.left, U)ˣ)
      (hX : X.hom.relativeDimensionFunction delta (genericPoint X.left) = n)
      (hs : Units.map (X.left.germToFunctionField U).hom s = f),
      @AlgebraicCycle.principal (closure X U s)
          (LocallyOfFiniteType.isLocallyNoetherian (fst X U s ≫ X.hom)) inferInstance
          (function X U s f) =
        (@Scheme.IdealSheafData.associatedCycle (closure X U s)
            (LocallyOfFiniteType.isLocallyNoetherian (fst X U s ≫ X.hom))
            (zeroDivisor X U s)
            ((fst X U s ≫ X.hom).relativeDimensionFunction delta) (n - 1) :
          AlgebraicCycle (closure X U s) ℤ) -
        (@Scheme.IdealSheafData.associatedCycle (closure X U s)
            (LocallyOfFiniteType.isLocallyNoetherian (fst X U s ≫ X.hom))
            (infinityDivisor X U s)
            ((fst X U s ≫ X.hom).relativeDimensionFunction delta) (n - 1) :
          AlgebraicCycle (closure X U s) ℤ))

/- Lemma 42.18.2 (6): the principal divisor of `f` on `X` is the proper pushforward
of its principal divisor on the graph closure. -/
@[stacks 02RQ] #check
  (AlgebraicGeometry.RationalFunctionGraph.principal_eq_pushforward :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
      [IsDimensionFunction delta] (X : Over S) [LocallyOfFiniteType X.hom]
      [IsIntegral X.left] (n : ℤ) (f : X.left.functionFieldˣ)
      (U : X.left.Opens) [Nonempty U] (s : Γ(X.left, U)ˣ)
      (hX : X.hom.relativeDimensionFunction delta (genericPoint X.left) = n)
      (hs : Units.map (X.left.germToFunctionField U).hom s = f),
      @AlgebraicCycle.principal X.left
          (LocallyOfFiniteType.isLocallyNoetherian X.hom) inferInstance f =
        AlgebraicCycle.map (fst X U s)
          ((fst X U s ≫ X.hom).relativeDimensionFunction delta)
          (X.hom.relativeDimensionFunction delta)
          (@AlgebraicCycle.principal (closure X U s)
            (LocallyOfFiniteType.isLocallyNoetherian (fst X U s ≫ X.hom))
            inferInstance (function X U s f)))

/- Lemma 42.18.2 (7): viewing `Y₀` and `Y∞` as their closed images in `X`, the
principal divisor of `f` is their difference in degree `n - 1`. -/
@[stacks 02RQ] #check
  (AlgebraicGeometry.RationalFunctionGraph.principal_eq_zeroImage_sub_infinityImage :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
      [IsDimensionFunction delta] (X : Over S) [LocallyOfFiniteType X.hom]
      [IsIntegral X.left] (n : ℤ) (f : X.left.functionFieldˣ)
      (U : X.left.Opens) [Nonempty U] (s : Γ(X.left, U)ˣ)
      (hX : X.hom.relativeDimensionFunction delta (genericPoint X.left) = n)
      (hs : Units.map (X.left.germToFunctionField U).hom s = f),
      @AlgebraicCycle.principal X.left
          (LocallyOfFiniteType.isLocallyNoetherian X.hom) inferInstance f =
        (@Scheme.IdealSheafData.associatedCycle X.left
            (LocallyOfFiniteType.isLocallyNoetherian X.hom) (zeroImage X U s)
            (X.hom.relativeDimensionFunction delta) (n - 1) : AlgebraicCycle X.left ℤ) -
        (@Scheme.IdealSheafData.associatedCycle X.left
            (LocallyOfFiniteType.isLocallyNoetherian X.hom) (infinityImage X U s)
            (X.hom.relativeDimensionFunction delta) (n - 1) :
          AlgebraicCycle X.left ℤ))

end AlgebraicGeometry.RationalFunctionGraph
