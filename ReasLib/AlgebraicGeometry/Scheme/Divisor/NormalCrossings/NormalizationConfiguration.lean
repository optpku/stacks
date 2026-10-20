module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.NormalCrossings.EtaleLocal
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberPower.Configuration
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.LocallyNoetherian
public import ReasLib.AlgebraicGeometry.Scheme.Regular

/-!
# Normal crossings divisors and normalization configurations

Normal crossings divisors are characterized by the pairwise-distinct loci in the positive
fibre powers of their normalizations.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

open Scheme.Hom.FiberPower

/-- A closed subscheme of a locally Noetherian scheme is a normal crossings divisor exactly
when it is reduced, its normalization is unramified, and every positive pairwise-distinct
normalization fibre power is regular and locally complete intersection over the ambient scheme,
with conormal sheaf of rank equal to the number of factors. -/
theorem isNormalCrossingsDivisor_iff_normalizationConfiguration
    {X : Scheme.{u}} [IsLocallyNoetherian X] (D : X.IdealSheafData) :
    IsNormalCrossingsDivisor D ↔
      IsReduced D.subscheme ∧
        Unramified D.subscheme.normalizationTo ∧
          ∀ n : ℕ+,
            Scheme.Regular
                (configurationOpen D.subscheme.normalizationTo n).toScheme ∧
              LocallyOfType RingHom.IsLocalCompleteIntersection
                (configurationToBase D.subscheme.normalizationTo n ≫ D.subschemeι) ∧
              Scheme.Modules.IsFiniteLocallyFreeOfRank n
                (Scheme.Hom.conormalSheaf
                  (configurationToBase D.subscheme.normalizationTo n ≫ D.subschemeι)) := sorry

namespace IsNormalCrossingsDivisor

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- A normal crossings divisor is reduced. -/
@[instance]
theorem instIsReducedSubscheme (D : X.IdealSheafData) [IsNormalCrossingsDivisor D] :
    IsReduced D.subscheme := sorry

/-- The normalization of a normal crossings divisor is unramified. -/
@[instance]
theorem instUnramifiedNormalization (D : X.IdealSheafData) [IsNormalCrossingsDivisor D] :
    Unramified D.subscheme.normalizationTo := sorry

/-- Every positive pairwise-distinct normalization fibre power of a normal crossings divisor
is regular. -/
@[instance]
theorem instRegularConfiguration (D : X.IdealSheafData) [IsNormalCrossingsDivisor D]
    (n : ℕ+) :
    Scheme.Regular
      (configurationOpen D.subscheme.normalizationTo n).toScheme := sorry

/-- The map from every positive pairwise-distinct normalization fibre power of a normal
crossings divisor to the ambient scheme is locally of complete-intersection type. -/
@[instance]
theorem instLciConfiguration (D : X.IdealSheafData) [IsNormalCrossingsDivisor D]
    (n : ℕ+) :
    LocallyOfType RingHom.IsLocalCompleteIntersection
      (configurationToBase D.subscheme.normalizationTo n ≫ D.subschemeι) := sorry

/-- The conormal sheaf of every positive configuration map of a normal crossings divisor has
rank equal to the number of factors. -/
@[instance]
theorem instConfigurationConormalRank (D : X.IdealSheafData)
    [IsNormalCrossingsDivisor D] (n : ℕ+) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank n
      (Scheme.Hom.conormalSheaf
        (configurationToBase D.subscheme.normalizationTo n ≫ D.subschemeι)) := sorry

/-- A reduced closed subscheme whose normalization is unramified and whose positive
pairwise-distinct normalization fibre powers are regular local complete intersections with
conormal rank equal to the number of factors is a normal crossings divisor. -/
theorem of_normalizationConfiguration (D : X.IdealSheafData)
    (h_reduced : IsReduced D.subscheme)
    (h_unramified : Unramified D.subscheme.normalizationTo)
    (h_regular : ∀ n : ℕ+, Scheme.Regular
      (configurationOpen D.subscheme.normalizationTo n).toScheme)
    (h_lci : ∀ n : ℕ+, LocallyOfType RingHom.IsLocalCompleteIntersection
      (configurationToBase D.subscheme.normalizationTo n ≫ D.subschemeι))
    (h_conormal : ∀ n : ℕ+, Scheme.Modules.IsFiniteLocallyFreeOfRank n
      (Scheme.Hom.conormalSheaf
        (configurationToBase D.subscheme.normalizationTo n ≫ D.subschemeι))) :
    IsNormalCrossingsDivisor D := sorry

end IsNormalCrossingsDivisor

end AlgebraicGeometry
