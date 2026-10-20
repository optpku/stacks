module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.AssociatedCycle
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Noetherian
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

section

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]

/- Definition 82.5.2 (1): In Situation 82.2.1, for good `X / B` and a closed
subspace `Y ⊂ X`, the multiplicity of an irreducible component of `Y` is the
length of `𝒪_Y` at its generic point. -/
@[stacks 0EE9]
#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.componentMultiplicity :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X],
    (Y : ClosedSubspace X) → genericPoints Y.X → ℕ)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.componentMultiplicity_eq_length :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    (Y : ClosedSubspace X) [IsDecent Y.X] (η : genericPoints Y.X)
    (xbar : GeometricPoint Y.X), xbar.liesOver η.1 →
      (ClosedSubspace.componentMultiplicity Y η : ℕ∞) =
        Modules.lengthAtGeometricPoint
          (SheafOfModules.unit (structureSheaf Y.X) : Y.X.Modules) xbar)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.hasLengthAt_componentMultiplicity :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    (Y : ClosedSubspace X) [IsDecent Y.X] (η : genericPoints Y.X),
      Modules.hasLengthAt (SheafOfModules.unit (structureSheaf Y.X) : Y.X.Modules) η.1
        (ClosedSubspace.componentMultiplicity Y η))

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.componentMultiplicity_pos :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    (Y : ClosedSubspace X) [IsDecent Y.X] (η : genericPoints Y.X),
      0 < ClosedSubspace.componentMultiplicity Y η)

/- Definition 82.5.2 (2): If `dim_δ(Y) ≤ k`, the associated `k`-cycle is the
multiplicity-weighted sum of the `δ`-dimension-`k` irreducible components of `Y`. -/
@[stacks 0EE9]
#check (AlgebraicGeometry.AlgebraicSpace.Hom.closedSubspaceCycle f δ :
  (Y : ClosedSubspace X) → (k : ℤ) →
    AlgebraicGeometry.AlgebraicSpace.Hom.closedSubspaceDeltaDimension f δ Y ≤ (k : EInt) →
      Function.locallyFinsupp (Points X) ℤ)

end
