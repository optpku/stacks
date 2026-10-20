module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.FlatPullback.Principal
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom TopologicalSpace

universe u

/- Lemma 82.16.1. Flat pullback of a principal divisor is the multiplicity-weighted
sum of the pushed-forward principal divisors on the irreducible components. -/
@[stacks 0EQA] #check (AlgebraicGeometry.AlgebraicSpace.Hom.flatPullback_principalDivisor :
  ∀ {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) [IsIntegral Y] (k : ℤ)
    (hY : closedSubspaceDeltaDimension pY δ (ClosedSubspace.id Y) = (k : EInt))
    (g : (RationalFunction Y)ˣ),
    (flatPullbackHom pY pX δ f r hf (k - 1)
        ⟨@principalCycle S Y (LocallyOfFiniteType.isLocallyNoetherian pY)
          inferInstance g,
          principalCycle_mem pY δ k hY g⟩ :
        Function.locallyFinsupp (Points X) ℤ) =
      AlgebraicCycle.locallyFiniteSum
        (fun η : genericPoints X ↦
          flatComponentPrincipal pX f r g η)
        (locallyFinite_flatComponentPrincipal pX f r g))
