module

public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization.NeighborhoodComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.FormalFunctions
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology.Map
public import ReasLib.Topology.Sheaf.Cohomology.SupportedRestriction

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineAlgebraizationSetup

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- The diagram `V ↦ H^p(V, M)` over neighborhoods of the restricted closed fiber. -/
noncomputable abbrev neighborhoodCohomologyDiagram (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (p : ℕ) :
    (OpenNeighborhoods S)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (OrderHom.Subtype.val
      (fun V : S.U.toScheme.Opens ↦ ((idealOnOpen S).support : Set S.U) ⊆ V)).toFunctor.op ⋙
    ((RingedSpace.moduleUnderlyingSheaf S.U.toScheme.toRingedSpace).obj M).cohomologyPresheaf p

/-- At a neighborhood `V`, `neighborhoodCohomologyDiagram S M p` is `H^p(V, M)`. -/
theorem neighborhoodCohomologyDiagram_obj (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (p : ℕ) (V : (OpenNeighborhoods S)ᵒᵖ) :
    (neighborhoodCohomologyDiagram S M p).obj V =
      ((RingedSpace.moduleUnderlyingSheaf S.U.toScheme.toRingedSpace).obj M).H' p V.unop.1 :=
  sorry

/-- Each ideal-power quotient vanishes on the complement of the restricted ideal's support. -/
theorem quotientRestrictionToComplement_eq_zero (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (n : ℕ) :
    TopCat.Sheaf.ClosedSubset.SectionsWithSupport.restrictionToComplement
      (idealOnOpen S).support.isClosed
      ((RingedSpace.moduleUnderlyingSheaf S.U.toScheme.toRingedSpace).obj
        (Scheme.Hom.IdealPowerCohomology.Quotient.stage S.I S.U.ι M n)) = 0 := sorry

/-- The map from `H^p(V, M)` to the `n`th global quotient-cohomology stage. -/
noncomputable def neighborhoodStageMap (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (p n : ℕ) (V : OpenNeighborhoods S) :
    (neighborhoodCohomologyDiagram S M p).obj (op V) ⟶
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).obj
        ((Scheme.Hom.IdealPowerCohomology.Quotient.tower S.I S.U.ι M p).obj (op n)) :=
  CategoryTheory.Sheaf.cohomologyMap
      ((RingedSpace.moduleUnderlyingSheaf S.U.toScheme.toRingedSpace).map
        (Scheme.Hom.IdealPowerCohomology.Quotient.projection S.I S.U.ι M n)) p V.1 ≫
    (TopCat.Sheaf.Cohomology.restrictionIsoOfSupport
      (idealOnOpen S).support.isClosed
      ((RingedSpace.moduleUnderlyingSheaf S.U.toScheme.toRingedSpace).obj
        (Scheme.Hom.IdealPowerCohomology.Quotient.stage S.I S.U.ι M n))
      (quotientRestrictionToComplement_eq_zero S M n) p V.1 V.2).inv ≫
    (eqToIso
      (Scheme.Hom.cohomologyForget_obj_eq S.U.ι
        (Scheme.Hom.IdealPowerCohomology.Quotient.stage S.I S.U.ι M n) p).symm).hom

/-- The neighborhood stage maps commute with restriction between neighborhoods. -/
theorem neighborhoodStageMap_naturality (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (p n : ℕ)
    {V W : (OpenNeighborhoods S)ᵒᵖ} (g : V ⟶ W) :
    (neighborhoodCohomologyDiagram S M p).map g ≫
        neighborhoodStageMap S M p n W.unop =
      neighborhoodStageMap S M p n V.unop := sorry

/-- The `n`th quotient-cohomology stage is a cocone over neighborhood cohomology. -/
noncomputable def neighborhoodStageCocone (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (p n : ℕ) :
    Cocone (neighborhoodCohomologyDiagram S M p) where
  pt := (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).obj
    ((Scheme.Hom.IdealPowerCohomology.Quotient.tower S.I S.U.ι M p).obj (op n))
  ι :=
    { app := fun V ↦ neighborhoodStageMap S M p n V.unop
      naturality := fun _ _ g ↦ neighborhoodStageMap_naturality S M p n g }

/-- The map from the neighborhood colimit to the `n`th quotient-cohomology stage. -/
noncomputable def neighborhoodProjection (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (p n : ℕ) :
    colimit (neighborhoodCohomologyDiagram S M p) ⟶
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).obj
        ((Scheme.Hom.IdealPowerCohomology.Quotient.tower S.I S.U.ι M p).obj (op n)) :=
  colimit.desc _ (neighborhoodStageCocone S M p n)

/-- The maps from neighborhood cohomology to quotient cohomology commute with the
ideal-power transitions. -/
theorem neighborhoodProjection_naturality (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (p n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj
        (colimit (neighborhoodCohomologyDiagram S M p))).map
          (homOfLE (Nat.le_add_right n 1)).op ≫ neighborhoodProjection S M p n =
      neighborhoodProjection S M p (n + 1) ≫
        (Scheme.Hom.IdealPowerCohomology.Quotient.tower S.I S.U.ι M p ⋙
          forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).map
            (homOfLE (Nat.le_add_right n 1)).op := sorry

/-- The canonical cone from the colimit of neighborhood cohomology to the underlying
quotient-cohomology system. -/
noncomputable def neighborhoodCone (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (p : ℕ) :
    Cone (Scheme.Hom.IdealPowerCohomology.Quotient.tower S.I S.U.ι M p ⋙
      forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}) where
  pt := colimit (neighborhoodCohomologyDiagram S M p)
  π := NatTrans.ofOpSequence (neighborhoodProjection S M p)
    (neighborhoodProjection_naturality S M p)

/-- The canonical comparison from neighborhood cohomology to the underlying additive group of
`lim_n H^p(S.U, M / I ^ n M)`. -/
noncomputable def neighborhoodCohomologyComparison (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (p : ℕ) :
    colimit (neighborhoodCohomologyDiagram S M p) ⟶
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).obj
        (limit (Scheme.Hom.IdealPowerCohomology.Quotient.tower S.I S.U.ι M p)) :=
  limit.lift _ (neighborhoodCone S M p) ≫
    (preservesLimitIso (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})
      (Scheme.Hom.IdealPowerCohomology.Quotient.tower S.I S.U.ι M p)).inv

/-- After transport through the forgetful limit isomorphism, the `n`th projection of the
neighborhood comparison is `neighborhoodProjection S M p n`. -/
theorem neighborhoodCohomologyComparison_π (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (p n : ℕ) :
    neighborhoodCohomologyComparison S M p ≫
        (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).map
          (limit.π (Scheme.Hom.IdealPowerCohomology.Quotient.tower S.I S.U.ι M p) (op n)) =
      neighborhoodProjection S M p n := sorry

end AlgebraicGeometry.AffineAlgebraizationSetup
