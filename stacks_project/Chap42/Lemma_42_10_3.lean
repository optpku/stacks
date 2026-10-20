module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.StructureSheafCycle
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 42.10.3: if a closed subscheme `Z` has `δ`-dimension at most `k`, then its
degree-`k` cycle equals the degree-`k` cycle associated to its pushed-forward structure sheaf. -/
@[stacks 02QY] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.cycle_eq_associatedCycle :
    {S X : Scheme.{u}} → (f : X ⟶ S) → [UniversallyCatenary S] →
      [LocallyOfFiniteType f] → (δ : S → ℤ) → [IsDimensionFunction δ] →
        (Z : X.IdealSheafData) → (k : ℤ) →
          (hZ : f.closedSubschemeDeltaDimension δ Z ≤ (k : EInt)) →
            -- Local instance justification (proof-local temporary data): `f` canonically supplies `IsLocallyNoetherian X`, but it is not inferable from `X` alone.
            letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
            (f.closedSubschemeCycle δ Z k hZ : AlgebraicCycle X ℤ) =
              (closedSubschemeStructureSheafOn Z).associatedCycle
                (f.relativeDimensionFunction δ) k)
