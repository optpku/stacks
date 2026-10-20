module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Principal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FunctionField.Dimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FunctionField.Norm
import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.GenericPoints.FunctionField

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicCycle

/-- A dominant proper morphism between integral schemes of the same relative dimension sends a
principal cycle to the principal cycle of the induced function-field norm. -/
theorem map_principal_of_proper
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral X.left] [IsIntegral Y.left] (n : ℤ) (p : X ⟶ Y)
    [IsProper p.left] [IsDominant p.left]
    (hX : X.hom.relativeDimensionFunction δ (genericPoint X.left) = n)
    (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = n)
    (f : X.left.functionFieldˣ) :
    -- Local instance justification (proof-local temporary data): local finite type over the locally Noetherian base `S` canonically makes `X.left` locally Noetherian.
    letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
    -- Local instance justification (proof-local temporary data): local finite type over the locally Noetherian base `S` canonically makes `Y.left` locally Noetherian.
    letI : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
    map p.left (X.hom.relativeDimensionFunction δ) (Y.hom.relativeDimensionFunction δ)
        (principal X.left f) =
      principal Y.left (p.left.inducedFunctionFieldNorm f) := sorry

end AlgebraicGeometry.AlgebraicCycle
