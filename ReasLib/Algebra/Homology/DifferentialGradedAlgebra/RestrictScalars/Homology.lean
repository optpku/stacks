module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Homology
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.RestrictScalars.Composition

/-!
# Homology under restriction of scalars for chain DGAs

This leaf specializes the canonical module-category homology comparison to the underlying chain
complex of a chain differential graded algebra. Restriction on chain-DGA morphisms supplies the
naturality interface, while vanishing statements remain expressed through the existing
ChainDGAlgebra.PositiveHomologyVanishes predicate.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uR uS uB

namespace ChainDGAlgebra.RestrictScalars

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]

/-- Tag 09PQ: homology of a chain DGA after restriction of scalars is canonically the
restriction of its original homology object. -/
@[stacks 09PQ "homology under restriction of scalars for chain DGAs"]
noncomputable def homologyIso
    (sigma : R →+* S) (B : ChainDGAlgebra.{uS, uB} S) (n : ℤ) :
    (B.restrictScalars sigma).homology n ≅
      (ModuleCat.restrictScalars sigma).obj (B.homology n) :=
  ModuleCat.restrictScalarsHomologyIso sigma B.toChainComplex n

/-- The restriction-of-scalars homology comparison is natural in chain-DGA morphisms. -/
@[reassoc, stacks 09PQ "naturality of restriction-of-scalars homology for chain DGAs"]
theorem homologyIso_hom_naturality
    (sigma : R →+* S) {B C : ChainDGAlgebra.{uS, uB} S}
    (phi : B ⟶ C) (n : ℤ) :
    HomologicalComplex.homologyMap (map sigma phi).toChainMap n ≫
        (homologyIso sigma C n).hom =
      (homologyIso sigma B n).hom ≫
        (ModuleCat.restrictScalars sigma).map
          (HomologicalComplex.homologyMap phi.toChainMap n) := sorry

/-- Tag 09PQ: homology in a fixed integer degree vanishes after restriction of scalars exactly
when it vanishes before restriction. -/
@[simp, stacks 09PQ "homology vanishing under restriction of scalars for chain DGAs"]
theorem homologyIsZero_iff
    (sigma : R →+* S) (B : ChainDGAlgebra.{uS, uB} S) (n : ℤ) :
    IsZero ((B.restrictScalars sigma).homology n) ↔
      IsZero (B.homology n) := sorry

/-- Tag 09PQ: restriction of scalars preserves and reflects vanishing of all positive
homology of a chain DGA. -/
@[simp, stacks 09PQ "positive homology under restriction of scalars for chain DGAs"]
theorem positiveHomologyVanishes_iff
    (sigma : R →+* S) (B : ChainDGAlgebra.{uS, uB} S) :
    (B.restrictScalars sigma).PositiveHomologyVanishes ↔
      B.PositiveHomologyVanishes := sorry

end ChainDGAlgebra.RestrictScalars
