module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology.Map
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.RingedSpace
public import ReasLib.Topology.Sheaf.Cohomology.Restriction
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import stacks_project.Chap51.Lemma_51_2_2_Cohomology
public import stacks_project.Chap52.Lemma_52_12_2_Comparison

/-!
# Cohomology comparison for affine algebraization

This file constructs the canonical maps from ordinary cohomology and from cohomology on
neighborhoods to the inverse limit of the positive ideal-power quotient cohomology system.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open SheafOfModules.RingedSite.IdealSheaf
open SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule

noncomputable section

universe u

namespace AlgebraicGeometry.AffineAlgebraizationSetup

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- The positive `I`-power quotient `M / I ^ (n + 1) M` on `S.U`. -/
noncomputable abbrev positiveQuotient (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (n : ℕ) : S.U.toScheme.Modules :=
  (Scheme.Modules.fromRingedSpace S.U.toScheme).obj
    (PowerQuotientModule.stage.{u, u, u} (idealOnOpen S).toSubobject
      ((Scheme.Modules.toRingedSpace S.U.toScheme).obj M) (n + 1))

/-- The canonical projection `M ⟶ M / I ^ (n + 1) M` on `S.U`. -/
noncomputable abbrev positiveQuotientProjection (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (n : ℕ) : M ⟶ positiveQuotient S M n :=
  (Scheme.Modules.fromRingedSpace S.U.toScheme).map
    (PowerQuotientModule.projection.{u, u, u} (idealOnOpen S).toSubobject
      ((Scheme.Modules.toRingedSpace S.U.toScheme).obj M) (n + 1))

/-- The transition
`M / I ^ (n + 2) M ⟶ M / I ^ (n + 1) M` on `S.U`. -/
noncomputable abbrev positiveQuotientTransition (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (n : ℕ) :
    positiveQuotient S M (n + 1) ⟶ positiveQuotient S M n :=
  (Scheme.Modules.fromRingedSpace S.U.toScheme).map
    (PowerQuotientModule.step.{u, u, u} (idealOnOpen S).toSubobject
      ((Scheme.Modules.toRingedSpace S.U.toScheme).obj M) (n + 1))

/-- The inverse system whose stage `n` is
`H^p(S.U, M / I ^ (n + 1) M)`, viewed as an `A`-module. -/
noncomputable def positiveCohomologySystem (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (p : ℕ) : SequentialInverseSystem (ModuleCat.{u} A) :=
  @Functor.ofOpSequence (ModuleCat.{u} A) _
    (fun n ↦ Scheme.Hom.cohomology S.U.ι (positiveQuotient S M n) p)
    (fun n ↦ (Scheme.Hom.cohomologyFunctor S.U.ι p).map
      (positiveQuotientTransition S M n))

/-- Stage `n` of `positiveCohomologySystem S M p` is
`H^p(S.U, M / I ^ (n + 1) M)`. -/
theorem positiveCohomologySystem_obj (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (p n : ℕ) :
    (positiveCohomologySystem S M p).obj (op n) =
      Scheme.Hom.cohomology S.U.ι (positiveQuotient S M n) p := sorry

/-- The degree-`p` cohomology map induced by
`M ⟶ M / I ^ (n + 1) M`. -/
noncomputable def cohomologyProjection (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (p n : ℕ) :
    Scheme.Hom.cohomology S.U.ι M p ⟶
      (positiveCohomologySystem S M p).obj (op n) :=
  (Scheme.Hom.cohomologyFunctor S.U.ι p).map
    (positiveQuotientProjection S M n)

/-- The cohomology projections commute with the positive ideal-power transitions. -/
theorem cohomologyProjection_naturality (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (p n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj (Scheme.Hom.cohomology S.U.ι M p)).map
          (homOfLE (Nat.le_add_right n 1)).op ≫ cohomologyProjection S M p n =
      cohomologyProjection S M p (n + 1) ≫
        (positiveCohomologySystem S M p).map
          (homOfLE (Nat.le_add_right n 1)).op := sorry

/-- The canonical cone from `H^p(S.U, M)` to the positive quotient-cohomology system. -/
noncomputable def cohomologyCone (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (p : ℕ) : Cone (positiveCohomologySystem S M p) where
  pt := Scheme.Hom.cohomology S.U.ι M p
  π := NatTrans.ofOpSequence (cohomologyProjection S M p)
    (cohomologyProjection_naturality S M p)

/-- The canonical comparison
`H^p(S.U, M) ⟶ lim_n H^p(S.U, M / I ^ (n + 1) M)`. -/
noncomputable def cohomologyComparison (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (p : ℕ) :
    Scheme.Hom.cohomology S.U.ι M p ⟶ limit (positiveCohomologySystem S M p) :=
  limit.lift _ (cohomologyCone S M p)

/-- Composing `cohomologyComparison S M p` with the `n`th limit projection gives the
corresponding quotient-cohomology projection. -/
theorem cohomologyComparison_π (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (p n : ℕ) :
    cohomologyComparison S M p ≫
        limit.π (positiveCohomologySystem S M p) (op n) =
      cohomologyProjection S M p n := sorry

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

/-- Restriction of a positive quotient from `S.U` to a neighborhood containing its support. -/
noncomputable abbrev positiveQuotientRestriction (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (p n : ℕ) (V : OpenNeighborhoods S) :
    ((RingedSpace.moduleUnderlyingSheaf S.U.toScheme.toRingedSpace).obj
        (positiveQuotient S M n)).H' p (⊤ : Opens S.U) ⟶
      ((RingedSpace.moduleUnderlyingSheaf S.U.toScheme.toRingedSpace).obj
        (positiveQuotient S M n)).H' p V.1 :=
  TopCat.Sheaf.Cohomology.restriction
    ((RingedSpace.moduleUnderlyingSheaf S.U.toScheme.toRingedSpace).obj
      (positiveQuotient S M n)) p le_top

/-- The pullback-pushforward unit along a neighborhood inclusion is invertible on a positive
quotient, whose support is contained in that neighborhood. -/
noncomputable instance positiveQuotient_unit_isIso
    (S : AffineAlgebraizationSetup A) (M : S.U.toScheme.Modules)
    (n : ℕ) (V : OpenNeighborhoods S) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction V.1.ι).unit.app
      (positiveQuotient S M n)) := sorry

/-- Restriction to a neighborhood containing the support of a positive quotient is an
isomorphism on cohomology. -/
noncomputable instance positiveQuotientRestriction_isIso
    (S : AffineAlgebraizationSetup A) (M : S.U.toScheme.Modules)
    (p n : ℕ) (V : OpenNeighborhoods S) :
    IsIso (positiveQuotientRestriction S M p n V) := sorry

/-- Ordinary cohomology of a positive quotient is the underlying additive group of the
corresponding `A`-module stage. -/
noncomputable def positiveCohomologyStageForgetIso (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (p n : ℕ) :
    ((RingedSpace.moduleUnderlyingSheaf S.U.toScheme.toRingedSpace).obj
        (positiveQuotient S M n)).H' p (⊤ : Opens S.U) ≅
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).obj
        ((positiveCohomologySystem S M p).obj (op n)) :=
  eqToIso
    (Scheme.Hom.cohomologyForget_obj_eq S.U.ι (positiveQuotient S M n) p).symm

/-- The map from `H^p(V, M)` to the `n`th global positive quotient-cohomology stage. -/
noncomputable def neighborhoodStageMap (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (p n : ℕ) (V : OpenNeighborhoods S) :
    (neighborhoodCohomologyDiagram S M p).obj (op V) ⟶
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).obj
        ((positiveCohomologySystem S M p).obj (op n)) :=
  CategoryTheory.Sheaf.cohomologyMap
      ((RingedSpace.moduleUnderlyingSheaf S.U.toScheme.toRingedSpace).map
        (positiveQuotientProjection S M n)) p V.1 ≫
    inv (positiveQuotientRestriction S M p n V) ≫
    (positiveCohomologyStageForgetIso S M p n).hom

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
    ((positiveCohomologySystem S M p).obj (op n))
  ι :=
    { app := fun V ↦ neighborhoodStageMap S M p n V.unop
      naturality := fun _ _ g ↦ neighborhoodStageMap_naturality S M p n g }

/-- The map from the neighborhood colimit to the `n`th quotient-cohomology stage. -/
noncomputable def neighborhoodProjection (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (p n : ℕ) :
    colimit (neighborhoodCohomologyDiagram S M p) ⟶
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).obj
        ((positiveCohomologySystem S M p).obj (op n)) :=
  colimit.desc _ (neighborhoodStageCocone S M p n)

/-- The maps from neighborhood cohomology to quotient cohomology commute with the positive
ideal-power transitions. -/
theorem neighborhoodProjection_naturality (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (p n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj
        (colimit (neighborhoodCohomologyDiagram S M p))).map
          (homOfLE (Nat.le_add_right n 1)).op ≫ neighborhoodProjection S M p n =
      neighborhoodProjection S M p (n + 1) ≫
        (positiveCohomologySystem S M p ⋙
          forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).map
            (homOfLE (Nat.le_add_right n 1)).op := sorry

/-- The canonical cone from the colimit of neighborhood cohomology to the underlying positive
quotient-cohomology system. -/
noncomputable def neighborhoodCone (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (p : ℕ) :
    Cone (positiveCohomologySystem S M p ⋙
      forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}) where
  pt := colimit (neighborhoodCohomologyDiagram S M p)
  π := NatTrans.ofOpSequence (neighborhoodProjection S M p)
    (neighborhoodProjection_naturality S M p)

/-- The canonical comparison from neighborhood cohomology to the underlying additive group of
`lim_n H^p(S.U, M / I ^ (n + 1) M)`. -/
noncomputable def neighborhoodCohomologyComparison (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (p : ℕ) :
    colimit (neighborhoodCohomologyDiagram S M p) ⟶
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).obj
        (limit (positiveCohomologySystem S M p)) :=
  limit.lift _ (neighborhoodCone S M p) ≫
    (preservesLimitIso (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})
      (positiveCohomologySystem S M p)).inv

/-- After transport through the forgetful limit isomorphism, the `n`th projection of the
neighborhood comparison is `neighborhoodProjection S M p n`. -/
theorem neighborhoodCohomologyComparison_π (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (p n : ℕ) :
    neighborhoodCohomologyComparison S M p ≫
        (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).map
          (limit.π (positiveCohomologySystem S M p) (op n)) =
      neighborhoodProjection S M p n := sorry

end AlgebraicGeometry.AffineAlgebraizationSetup
