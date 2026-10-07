module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.AffineCover
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AffineOpenCover

/- Lemma 30.4.2: a quasi-coherent module on a quasi-compact scheme with affine diagonal has
vanishing global cohomology in degrees at least the minimal number of affine opens needed to
cover the scheme. -/
@[stacks 01XI] #check (globalCohomology_isZero_of_number :
  ∀ (X : Scheme.{u}) [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (n : ℕ), number X ≤ n →
      IsZero (((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).H' n (⊤ : Opens X)))

#check (number_isLeast :
  ∀ (X : Scheme.{u}) [CompactSpace X], IsLeast {t | HasCard X t} (number X))

end AlgebraicGeometry.Scheme.AffineOpenCover
