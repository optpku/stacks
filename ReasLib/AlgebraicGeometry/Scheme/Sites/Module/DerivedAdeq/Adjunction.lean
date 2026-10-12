/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.SiteComparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.DerivedAdeq.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.LiftedStructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Restriction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.KFlat
public import ReasLib.Algebra.Homology.DerivedCategory.Adjunction
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Adjunction

/-!
# The derived adequate association--restriction adjunction

This module compares the lifted small-Zariski presentation of derived
quasicoherent modules with the carrier-lifted modules used by the canonical
restriction morphism from a big standard site.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- The canonical derived-category structure on modules over the lifted
small-Zariski presentation. -/
@[reducible]
noncomputable def smallRingDownSourceHasDerivedCategory (S : Scheme.{u}) :
    HasDerivedCategory
      (RingedSite.ModuleCat.{u + 1} (smallZariskiRingedSite S)) :=
  RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1} (smallZariskiRingedSite S)

/-- The canonical derived-category structure on carrier-lifted modules over
the original small-Zariski structure sheaf. -/
@[reducible]
noncomputable def smallRingDownTargetHasDerivedCategory (S : Scheme.{u}) :
    HasDerivedCategory
      (RingedSite.ModuleCat.{u + 1} (Scheme.Zariski.Small.ringedSite S)) :=
  RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1}
    (Scheme.Zariski.Small.ringedSite S)

/-- Objectwise, the lifted small-Zariski structure sheaf is the universe lift
of the original structure sheaf. -/
theorem smallRingDown_ring (S : Scheme.{u}) (U : S.smallZariskiSiteᵒᵖ) :
    (smallZariskiRingedSite S).structureSheaf.obj.obj U =
      Scheme.Site.ringUniverseLiftObj.{u, u + 1}
        ((Scheme.Zariski.Small.structureSheaf S).obj.obj U) := sorry

/-- The underlying function of the canonical map from an original
small-Zariski coefficient ring into its lifted presentation. -/
noncomputable def smallCoefficientLiftFun (S : Scheme.{u}) (U : S.smallZariskiSiteᵒᵖ)
    : (Scheme.Zariski.Small.structureSheaf S).obj.obj U →
      (smallZariskiRingedSite S).structureSheaf.obj.obj U :=
  fun r ↦ ULift.up r

/-- The coefficient lift preserves the multiplicative unit. -/
theorem smallCoefficientLift_map_one (S : Scheme.{u}) (U : S.smallZariskiSiteᵒᵖ) :
    smallCoefficientLiftFun S U 1 = 1 := sorry

/-- The coefficient lift preserves multiplication. -/
theorem smallCoefficientLift_map_mul (S : Scheme.{u}) (U : S.smallZariskiSiteᵒᵖ)
    (a b : (Scheme.Zariski.Small.structureSheaf S).obj.obj U) :
    smallCoefficientLiftFun S U (a * b) =
      smallCoefficientLiftFun S U a * smallCoefficientLiftFun S U b := sorry

/-- The coefficient lift preserves zero. -/
theorem smallCoefficientLift_map_zero (S : Scheme.{u}) (U : S.smallZariskiSiteᵒᵖ) :
    smallCoefficientLiftFun S U 0 = 0 := sorry

/-- The coefficient lift preserves addition. -/
theorem smallCoefficientLift_map_add (S : Scheme.{u}) (U : S.smallZariskiSiteᵒᵖ)
    (a b : (Scheme.Zariski.Small.structureSheaf S).obj.obj U) :
    smallCoefficientLiftFun S U (a + b) =
      smallCoefficientLiftFun S U a + smallCoefficientLiftFun S U b := sorry

/-- The canonical map from an original small-Zariski coefficient ring into
its lifted presentation. -/
noncomputable def smallCoefficientLift (S : Scheme.{u}) (U : S.smallZariskiSiteᵒᵖ) :
    (Scheme.Zariski.Small.structureSheaf S).obj.obj U →+*
      (smallZariskiRingedSite S).structureSheaf.obj.obj U where
  toFun := smallCoefficientLiftFun S U
  map_one' := smallCoefficientLift_map_one S U
  map_mul' := smallCoefficientLift_map_mul S U
  map_zero' := smallCoefficientLift_map_zero S U
  map_add' := smallCoefficientLift_map_add S U

/-- A module over the lifted small-Zariski structure sheaf, regarded as a
module over the original structure sheaf by restriction along `R ≃+* ULift R`. -/
noncomputable abbrev smallRingDownObj (S : Scheme.{u})
    (M : RingedSite.ModuleCat.{u + 1} (smallZariskiRingedSite S))
    (U : S.smallZariskiSiteᵒᵖ) :
    ModuleCat.{u + 1} ((Scheme.Zariski.Small.structureSheaf S).obj.obj U) :=
  (ModuleCat.restrictScalars
    (smallCoefficientLift S U)).obj (M.val.obj U)

/-- Restriction of a lifted small-Zariski module morphism to the original
coefficient ring. -/
noncomputable def smallRingDownMap (S : Scheme.{u})
    {M N : RingedSite.ModuleCat.{u + 1} (smallZariskiRingedSite S)}
    (f : M ⟶ N) (U : S.smallZariskiSiteᵒᵖ) :
    smallRingDownObj S M U ⟶ smallRingDownObj S N U :=
  let source : ModuleCat.{u + 1}
      ((Scheme.Zariski.Small.structureSheaf S).obj.obj U) :=
    smallRingDownObj S M U
  let target : ModuleCat.{u + 1}
      ((Scheme.Zariski.Small.structureSheaf S).obj.obj U) :=
    smallRingDownObj S N U
  @ModuleCat.ofHom _ _ (source : Type _) (target : Type _)
    (ModuleCat.isAddCommGroup source) (ModuleCat.isModule source)
    (ModuleCat.isAddCommGroup target) (ModuleCat.isModule target)
    { toFun := fun x ↦ f.val.app U x
      map_add' := sorry
      map_smul' := sorry }

/-- The target of a restriction map after forgetting the lift of the
small-Zariski coefficient ring. -/
noncomputable abbrev smallRingDownRestrictionTarget (S : Scheme.{u})
    (M : RingedSite.ModuleCat.{u + 1} (smallZariskiRingedSite S))
    {U V : S.smallZariskiSiteᵒᵖ} (f : U ⟶ V) :=
  (ModuleCat.restrictScalars
    ((Scheme.Zariski.Small.structureSheaf S).obj.map f).hom).obj
      (smallRingDownObj S M V)

/-- Restriction maps for the small-Zariski coefficient-ring comparison. -/
noncomputable def smallRingDownRestrictionMap (S : Scheme.{u})
    (M : RingedSite.ModuleCat.{u + 1} (smallZariskiRingedSite S))
    {U V : S.smallZariskiSiteᵒᵖ} (f : U ⟶ V) :
    smallRingDownObj S M U ⟶ smallRingDownRestrictionTarget S M f :=
  let source : ModuleCat.{u + 1}
      ((Scheme.Zariski.Small.structureSheaf S).obj.obj U) :=
    smallRingDownObj S M U
  let target : ModuleCat.{u + 1}
      ((Scheme.Zariski.Small.structureSheaf S).obj.obj U) :=
    smallRingDownRestrictionTarget S M f
  @ModuleCat.ofHom _ _ (source : Type _) (target : Type _)
    (ModuleCat.isAddCommGroup source) (ModuleCat.isModule source)
    (ModuleCat.isAddCommGroup target) (ModuleCat.isModule target)
    { toFun := fun x ↦ M.val.map f x
      map_add' := sorry
      map_smul' := sorry }

/-- Forgetting the universe lift of the coefficient rings in a small-Zariski
module presheaf. -/
noncomputable def smallRingDownPresheaf (S : Scheme.{u})
    (M : RingedSite.ModuleCat.{u + 1} (smallZariskiRingedSite S)) :
    _root_.PresheafOfModules.{u + 1}
      (Scheme.Zariski.Small.structureSheaf S).obj where
  obj := smallRingDownObj S M
  map := smallRingDownRestrictionMap S M
  map_id := sorry
  map_comp := sorry

/-- Restriction along the coefficient-ring equivalences preserves the sheaf
condition. -/
theorem smallRingDownPresheaf_isSheaf (S : Scheme.{u})
    (M : RingedSite.ModuleCat.{u + 1} (smallZariskiRingedSite S)) :
    Presheaf.IsSheaf S.smallZariskiTopology
      (smallRingDownPresheaf S M).presheaf := sorry

/-- Forgetting the coefficient-ring lift of a small-Zariski module sheaf. -/
noncomputable def smallRingDownSheafObj (S : Scheme.{u})
    (M : RingedSite.ModuleCat.{u + 1} (smallZariskiRingedSite S)) :
    RingedSite.ModuleCat.{u + 1} (Scheme.Zariski.Small.ringedSite S) :=
  ⟨smallRingDownPresheaf S M, smallRingDownPresheaf_isSheaf S M⟩

/-- Forgetting the coefficient-ring lift on a morphism of small-Zariski
module sheaves. -/
noncomputable def smallRingDownSheafMap (S : Scheme.{u})
    {M N : RingedSite.ModuleCat.{u + 1} (smallZariskiRingedSite S)}
    (f : M ⟶ N) : smallRingDownSheafObj S M ⟶ smallRingDownSheafObj S N :=
  ⟨fun U ↦ smallRingDownMap S f U, sorry⟩

/-- The concrete coefficient-ring comparison from the lifted to the original
small-Zariski presentation. -/
noncomputable def smallRingDown (S : Scheme.{u}) :
    RingedSite.ModuleCat.{u + 1} (smallZariskiRingedSite S) ⥤
      RingedSite.ModuleCat.{u + 1} (Scheme.Zariski.Small.ringedSite S) where
  obj := smallRingDownSheafObj S
  map := smallRingDownSheafMap S
  map_id := sorry
  map_comp := sorry

/-- The underlying function of the canonical map from a lifted small-Zariski
coefficient ring back to the original coefficient ring. -/
noncomputable def smallRingDownMapRingFun (S : Scheme.{u}) (U : S.smallZariskiSiteᵒᵖ)
    : (smallZariskiRingedSite S).structureSheaf.obj.obj U →
      (Scheme.Zariski.Small.structureSheaf S).obj.obj U :=
  fun r ↦ r.down

/-- The coefficient descent map preserves the multiplicative unit. -/
theorem smallRingDownMapRing_map_one (S : Scheme.{u}) (U : S.smallZariskiSiteᵒᵖ) :
    smallRingDownMapRingFun S U 1 = 1 := sorry

/-- The coefficient descent map preserves multiplication. -/
theorem smallRingDownMapRing_map_mul (S : Scheme.{u}) (U : S.smallZariskiSiteᵒᵖ)
    (a b : (smallZariskiRingedSite S).structureSheaf.obj.obj U) :
    smallRingDownMapRingFun S U (a * b) =
      smallRingDownMapRingFun S U a * smallRingDownMapRingFun S U b := sorry

/-- The coefficient descent map preserves zero. -/
theorem smallRingDownMapRing_map_zero (S : Scheme.{u}) (U : S.smallZariskiSiteᵒᵖ) :
    smallRingDownMapRingFun S U 0 = 0 := sorry

/-- The coefficient descent map preserves addition. -/
theorem smallRingDownMapRing_map_add (S : Scheme.{u}) (U : S.smallZariskiSiteᵒᵖ)
    (a b : (smallZariskiRingedSite S).structureSheaf.obj.obj U) :
    smallRingDownMapRingFun S U (a + b) =
      smallRingDownMapRingFun S U a + smallRingDownMapRingFun S U b := sorry

/-- The canonical map from a lifted small-Zariski coefficient ring back to
the original coefficient ring. -/
noncomputable def smallRingDownMapRing (S : Scheme.{u})
    (U : S.smallZariskiSiteᵒᵖ) :
    (smallZariskiRingedSite S).structureSheaf.obj.obj U →+*
      (Scheme.Zariski.Small.structureSheaf S).obj.obj U where
  toFun := smallRingDownMapRingFun S U
  map_one' := smallRingDownMapRing_map_one S U
  map_mul' := smallRingDownMapRing_map_mul S U
  map_zero' := smallRingDownMapRing_map_zero S U
  map_add' := smallRingDownMapRing_map_add S U

/-- An original-coefficient small-Zariski module, regarded over the lifted
coefficient ring by restriction along `ULift R ≃+* R`. -/
noncomputable abbrev smallRingUpObj (S : Scheme.{u})
    (M : RingedSite.ModuleCat.{u + 1} (Scheme.Zariski.Small.ringedSite S))
    (U : S.smallZariskiSiteᵒᵖ) :
    ModuleCat.{u + 1}
      ((smallZariskiRingedSite S).structureSheaf.obj.obj U) :=
  (ModuleCat.restrictScalars (smallRingDownMapRing S U)).obj (M.val.obj U)

/-- Extension of an original-coefficient module morphism to the lifted
small-Zariski coefficient presentation. -/
noncomputable def smallRingUpMap (S : Scheme.{u})
    {M N : RingedSite.ModuleCat.{u + 1}
      (Scheme.Zariski.Small.ringedSite S)}
    (f : M ⟶ N) (U : S.smallZariskiSiteᵒᵖ) :
    smallRingUpObj S M U ⟶ smallRingUpObj S N U :=
  let source : ModuleCat.{u + 1}
      ((smallZariskiRingedSite S).structureSheaf.obj.obj U) :=
    smallRingUpObj S M U
  let target : ModuleCat.{u + 1}
      ((smallZariskiRingedSite S).structureSheaf.obj.obj U) :=
    smallRingUpObj S N U
  @ModuleCat.ofHom _ _ (source : Type _) (target : Type _)
    (ModuleCat.isAddCommGroup source) (ModuleCat.isModule source)
    (ModuleCat.isAddCommGroup target) (ModuleCat.isModule target)
    { toFun := fun x ↦ f.val.app U x
      map_add' := sorry
      map_smul' := sorry }

/-- The target of a restriction map after restoring the lifted
small-Zariski coefficient ring. -/
noncomputable abbrev smallRingUpRestrictionTarget (S : Scheme.{u})
    (M : RingedSite.ModuleCat.{u + 1} (Scheme.Zariski.Small.ringedSite S))
    {U V : S.smallZariskiSiteᵒᵖ} (f : U ⟶ V) :=
  (ModuleCat.restrictScalars
    ((smallZariskiRingedSite S).structureSheaf.obj.map f).hom).obj
      (smallRingUpObj S M V)

/-- Restriction maps after restoring the lifted small-Zariski coefficient
ring. -/
noncomputable def smallRingUpRestrictionMap (S : Scheme.{u})
    (M : RingedSite.ModuleCat.{u + 1} (Scheme.Zariski.Small.ringedSite S))
    {U V : S.smallZariskiSiteᵒᵖ} (f : U ⟶ V) :
    smallRingUpObj S M U ⟶ smallRingUpRestrictionTarget S M f :=
  let source : ModuleCat.{u + 1}
      ((smallZariskiRingedSite S).structureSheaf.obj.obj U) :=
    smallRingUpObj S M U
  let target : ModuleCat.{u + 1}
      ((smallZariskiRingedSite S).structureSheaf.obj.obj U) :=
    smallRingUpRestrictionTarget S M f
  @ModuleCat.ofHom _ _ (source : Type _) (target : Type _)
    (ModuleCat.isAddCommGroup source) (ModuleCat.isModule source)
    (ModuleCat.isAddCommGroup target) (ModuleCat.isModule target)
    { toFun := fun x ↦ M.val.map f x
      map_add' := sorry
      map_smul' := sorry }

/-- Restoring the lifted coefficient rings in a small-Zariski module
presheaf. -/
noncomputable def smallRingUpPresheaf (S : Scheme.{u})
    (M : RingedSite.ModuleCat.{u + 1} (Scheme.Zariski.Small.ringedSite S)) :
    _root_.PresheafOfModules.{u + 1}
      (smallZariskiRingedSite S).structureSheaf.obj where
  obj := smallRingUpObj S M
  map := smallRingUpRestrictionMap S M
  map_id := sorry
  map_comp := sorry

/-- Restoring the lifted coefficient rings preserves the sheaf condition. -/
theorem smallRingUpPresheaf_isSheaf (S : Scheme.{u})
    (M : RingedSite.ModuleCat.{u + 1}
      (Scheme.Zariski.Small.ringedSite S)) :
    Presheaf.IsSheaf S.smallZariskiTopology
      (smallRingUpPresheaf S M).presheaf := sorry

/-- Restore the lifted coefficient rings on a small-Zariski module sheaf. -/
noncomputable def smallRingUpSheafObj (S : Scheme.{u})
    (M : RingedSite.ModuleCat.{u + 1} (Scheme.Zariski.Small.ringedSite S)) :
    RingedSite.ModuleCat.{u + 1} (smallZariskiRingedSite S) :=
  ⟨smallRingUpPresheaf S M, smallRingUpPresheaf_isSheaf S M⟩

/-- Restore the lifted coefficient rings on a morphism of small-Zariski
module sheaves. -/
noncomputable def smallRingUpSheafMap (S : Scheme.{u})
    {M N : RingedSite.ModuleCat.{u + 1}
      (Scheme.Zariski.Small.ringedSite S)}
    (f : M ⟶ N) : smallRingUpSheafObj S M ⟶ smallRingUpSheafObj S N :=
  ⟨fun U ↦ smallRingUpMap S f U, sorry⟩

/-- The concrete coefficient-ring comparison from the original to the
lifted small-Zariski presentation. -/
noncomputable def smallRingUp (S : Scheme.{u}) :
    RingedSite.ModuleCat.{u + 1} (Scheme.Zariski.Small.ringedSite S) ⥤
      RingedSite.ModuleCat.{u + 1} (smallZariskiRingedSite S) where
  obj := smallRingUpSheafObj S
  map := smallRingUpSheafMap S
  map_id := sorry
  map_comp := sorry

/-- A morphism from coefficient restriction corresponds to a morphism into
coefficient restoration. -/
noncomputable def smallRingHomEquiv (S : Scheme.{u})
    (M : RingedSite.ModuleCat.{u + 1} (smallZariskiRingedSite S))
    (N : RingedSite.ModuleCat.{u + 1} (Scheme.Zariski.Small.ringedSite S)) :
    ((smallRingDown S).obj M ⟶ N) ≃ (M ⟶ (smallRingUp S).obj N) where
  toFun f :=
    ⟨fun U ↦
      let source : ModuleCat.{u + 1}
          ((smallZariskiRingedSite S).structureSheaf.obj.obj U) := M.val.obj U
      let target : ModuleCat.{u + 1}
          ((smallZariskiRingedSite S).structureSheaf.obj.obj U) :=
        smallRingUpObj S N U
      @ModuleCat.ofHom _ _ (source : Type _) (target : Type _)
        (ModuleCat.isAddCommGroup source) (ModuleCat.isModule source)
        (ModuleCat.isAddCommGroup target) (ModuleCat.isModule target)
        { toFun := fun x ↦ f.val.app U x
          map_add' := sorry
          map_smul' := sorry }, sorry⟩
  invFun f :=
    ⟨fun U ↦
      let source : ModuleCat.{u + 1}
          ((Scheme.Zariski.Small.structureSheaf S).obj.obj U) :=
        smallRingDownObj S M U
      let target : ModuleCat.{u + 1}
          ((Scheme.Zariski.Small.structureSheaf S).obj.obj U) := N.val.obj U
      @ModuleCat.ofHom _ _ (source : Type _) (target : Type _)
        (ModuleCat.isAddCommGroup source) (ModuleCat.isModule source)
        (ModuleCat.isAddCommGroup target) (ModuleCat.isModule target)
        { toFun := fun x ↦ f.val.app U x
          map_add' := sorry
          map_smul' := sorry }, sorry⟩
  left_inv := sorry
  right_inv := sorry

/-- Restriction from lifted to original small-Zariski coefficient rings is
left adjoint to restoration of the lifted coefficients. -/
noncomputable def smallRingAdjunction (S : Scheme.{u}) :
    smallRingDown S ⊣ smallRingUp S :=
  Adjunction.mkOfHomEquiv
    { homEquiv := smallRingHomEquiv S
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

/-- The coefficient-ring comparison is exact. -/
theorem smallRingDown_exact (S : Scheme.{u}) :
    exactFunctor _ _ (smallRingDown S) := sorry

/-- The coefficient-ring comparison bundled as an exact functor. -/
noncomputable def smallRingDownExact (S : Scheme.{u}) :
    RingedSite.ModuleCat.{u + 1} (smallZariskiRingedSite S) ⥤ₑ
      RingedSite.ModuleCat.{u + 1} (Scheme.Zariski.Small.ringedSite S) :=
  ⟨smallRingDown S, smallRingDown_exact S⟩

/-- Restoring the lifted coefficient rings is exact. -/
theorem smallRingUp_exact (S : Scheme.{u}) :
    exactFunctor _ _ (smallRingUp S) := sorry

/-- Restoration of lifted coefficient rings bundled as an exact functor. -/
noncomputable def smallRingUpExact (S : Scheme.{u}) :
    RingedSite.ModuleCat.{u + 1} (Scheme.Zariski.Small.ringedSite S) ⥤ₑ
      RingedSite.ModuleCat.{u + 1} (smallZariskiRingedSite S) :=
  ⟨smallRingUp S, smallRingUp_exact S⟩

/-- The derived coefficient-ring comparison on the small Zariski site. -/
noncomputable def smallRingDownDerived (S : Scheme.{u}) :
    RingedSite.Hom.ModuleDerived.{u + 1} (smallZariskiRingedSite S) ⥤
      RingedSite.Hom.ModuleDerived.{u + 1}
        (Scheme.Zariski.Small.ringedSite S) :=
  @Functor.mapDerivedCategory
    (RingedSite.ModuleCat.{u + 1} (smallZariskiRingedSite S)) inferInstance inferInstance
      (smallRingDownSourceHasDerivedCategory S)
    (RingedSite.ModuleCat.{u + 1} (Scheme.Zariski.Small.ringedSite S)) inferInstance inferInstance
      (smallRingDownTargetHasDerivedCategory S)
    (smallRingDownExact S).obj inferInstance inferInstance inferInstance

/-- The derived coefficient-ring comparison restoring lifted rings. -/
noncomputable def smallRingUpDerived (S : Scheme.{u}) :
    RingedSite.Hom.ModuleDerived.{u + 1}
        (Scheme.Zariski.Small.ringedSite S) ⥤
      RingedSite.Hom.ModuleDerived.{u + 1} (smallZariskiRingedSite S) :=
  @Functor.mapDerivedCategory
    (RingedSite.ModuleCat.{u + 1} (Scheme.Zariski.Small.ringedSite S)) inferInstance
      inferInstance (smallRingDownTargetHasDerivedCategory S)
    (RingedSite.ModuleCat.{u + 1} (smallZariskiRingedSite S)) inferInstance inferInstance
      (smallRingDownSourceHasDerivedCategory S)
    (smallRingUpExact S).obj inferInstance inferInstance inferInstance

/-- The coefficient-ring adjunction induced on unbounded derived categories. -/
noncomputable def smallRingDerivedAdjunction (S : Scheme.{u}) :
    smallRingDownDerived S ⊣ smallRingUpDerived S :=
  -- Local instance justification (proof-local temporary data): finite-limit preservation for coefficient descent.
  letI : PreservesFiniteLimits (smallRingDown S) := (smallRingDownExact S).property.1
  -- Local instance justification (proof-local temporary data): finite-colimit preservation for coefficient descent.
  letI : PreservesFiniteColimits (smallRingDown S) := (smallRingDownExact S).property.2
  -- Local instance justification (proof-local temporary data): finite-limit preservation for coefficient restoration.
  letI : PreservesFiniteLimits (smallRingUp S) := (smallRingUpExact S).property.1
  -- Local instance justification (proof-local temporary data): finite-colimit preservation for coefficient restoration.
  letI : PreservesFiniteColimits (smallRingUp S) := (smallRingUpExact S).property.2
  -- Local instance justification (proof-local temporary data): additivity for coefficient descent.
  letI : (smallRingDown S).Additive :=
    Functor.additive_of_leftExact_or_rightExact (smallRingDown S)
      (Or.inl (smallRingDownExact S).property.1)
  -- Local instance justification (proof-local temporary data): additivity for coefficient restoration.
  letI : (smallRingUp S).Additive :=
    Functor.additive_of_leftExact_or_rightExact (smallRingUp S)
      (Or.inl (smallRingUpExact S).property.1)
  @CategoryTheory.Adjunction.mapDerivedCategory
    (RingedSite.ModuleCat.{u + 1} (smallZariskiRingedSite S)) inferInstance inferInstance
      (smallRingDownSourceHasDerivedCategory S)
    (RingedSite.ModuleCat.{u + 1} (Scheme.Zariski.Small.ringedSite S)) inferInstance inferInstance
      (smallRingDownTargetHasDerivedCategory S)
    (smallRingDown S) (smallRingUp S)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (smallRingAdjunction S)

end AlgebraicGeometry.Scheme.DerivedQCoh

namespace AlgebraicGeometry.Scheme.SiteRestriction.bigToZariski

/-- The canonical derived-category structure for lifted-carrier modules on the
big `τ`-site. -/
@[reducible]
noncomputable def bigSiteHasDerivedCategory
    (S : Scheme.{u}) (τ : StandardTopology) :
    HasDerivedCategory
      (RingedSite.ModuleCat.{u + 1} (StandardTopology.Big.ringedSite τ S)) :=
  RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1}
    (StandardTopology.Big.ringedSite τ S)

/-- Module direct image along `bigToZariski τ S`, with carriers in
`Type (u + 1)`, has its canonical inverse-image left adjoint. -/
theorem modulePushforwardIsRightAdjointLifted
    (S : Scheme.{u}) (τ : StandardTopology) :
    ((Scheme.SiteRestriction.bigToZariski τ S).modulePushforward.{u + 1}
      ).IsRightAdjoint := sorry

/-- Module inverse image along `bigToZariski τ S` admits its canonical
unbounded left-derived functor in the lifted carrier universe. -/
theorem modulePullbackHasLeftDerived
    (S : Scheme.{u}) (τ : StandardTopology) :
    Functor.HasLeftDerivedFunctor
      (@RingedSite.Hom.modulePullbackToDerived.{u + 1} _ _
        (Scheme.SiteRestriction.bigToZariski τ S) inferInstance
        (modulePushforwardIsRightAdjointLifted S τ))
      (RingedSite.Hom.ModuleQis.{u + 1}
        (Scheme.Zariski.Small.ringedSite S)) := sorry

/-- Direct image along `bigToZariski τ S` is exact: it is restriction from
the big site to the full small Zariski site. -/
theorem modulePushforward_exact
    (S : Scheme.{u}) (τ : StandardTopology) :
    exactFunctor _ _
      ((Scheme.SiteRestriction.bigToZariski τ S).modulePushforward.{u + 1}) := sorry

/-- Direct image along `bigToZariski τ S`, bundled with its exactness law. -/
noncomputable def modulePushforwardExact
    (S : Scheme.{u}) (τ : StandardTopology) :
    RingedSite.ModuleCat.{u + 1} (StandardTopology.Big.ringedSite τ S) ⥤ₑ
      RingedSite.ModuleCat.{u + 1} (Scheme.Zariski.Small.ringedSite S) :=
  ⟨(Scheme.SiteRestriction.bigToZariski τ S).modulePushforward,
    modulePushforward_exact S τ⟩

/-- The specified total left-derived model of inverse image along
`bigToZariski τ S`; its functor and localization counit are retained as data. -/
noncomputable def modulePullbackModel
    (S : Scheme.{u}) (τ : StandardTopology) :
    @RingedSite.Hom.PullbackModel.{u, u + 1} _ _
      (Scheme.SiteRestriction.bigToZariski τ S) inferInstance inferInstance
      (modulePushforwardIsRightAdjointLifted S τ) := by
  -- Local instance justification (proof-local temporary data): named left-derived certificate for the counit field.
  letI := modulePullbackHasLeftDerived S τ
  exact {
  functor := @RingedSite.Hom.modulePullbackDerived.{u + 1} _ _
    (Scheme.SiteRestriction.bigToZariski τ S) inferInstance inferInstance
    (modulePushforwardIsRightAdjointLifted S τ) (modulePullbackHasLeftDerived S τ)
  counit :=
    (@RingedSite.Hom.modulePullbackToDerived.{u + 1} _ _
      (Scheme.SiteRestriction.bigToZariski τ S) inferInstance
      (modulePushforwardIsRightAdjointLifted S τ)).totalLeftDerivedCounit
        (RingedSite.Hom.moduleLocalization.{u + 1}
          (Scheme.Zariski.Small.ringedSite S))
        (RingedSite.Hom.ModuleQis.{u + 1}
          (Scheme.Zariski.Small.ringedSite S))
  isLeftDerived := sorry }

/-- The specified total right-derived model of direct image along
`bigToZariski τ S`; its functor and localization unit are retained as data. -/
noncomputable def modulePushforwardModel
    (S : Scheme.{u}) (τ : StandardTopology) :
    CategoryTheory.Functor.RightDerived.Model
      (RingedSite.Hom.modulePushforwardToDerived.{u + 1}
        (Scheme.SiteRestriction.bigToZariski τ S))
      (RingedSite.Hom.moduleLocalization.{u + 1}
        (StandardTopology.Big.ringedSite τ S))
      (RingedSite.Hom.ModuleQis.{u + 1}
        (StandardTopology.Big.ringedSite τ S)) := by
  exact {
  functor := @Functor.mapDerivedCategory
    (RingedSite.ModuleCat.{u + 1} (StandardTopology.Big.ringedSite τ S)) inferInstance
      inferInstance (bigSiteHasDerivedCategory S τ)
    (RingedSite.ModuleCat.{u + 1} (Scheme.Zariski.Small.ringedSite S)) inferInstance
      inferInstance
      (AlgebraicGeometry.Scheme.DerivedQCoh.smallRingDownTargetHasDerivedCategory S)
    (modulePushforwardExact S τ).obj inferInstance inferInstance inferInstance
  unit := (@Functor.mapDerivedCategoryFactorsh
    (RingedSite.ModuleCat.{u + 1} (StandardTopology.Big.ringedSite τ S)) inferInstance
      inferInstance (bigSiteHasDerivedCategory S τ)
    (RingedSite.ModuleCat.{u + 1} (Scheme.Zariski.Small.ringedSite S)) inferInstance
      inferInstance
      (AlgebraicGeometry.Scheme.DerivedQCoh.smallRingDownTargetHasDerivedCategory S)
    (modulePushforwardExact S τ).obj inferInstance inferInstance inferInstance).inv
  isRightDerived := sorry }

/-- The pullback model is canonically independent of a second explicit
left-derived model. -/
noncomputable def modulePullbackModelIso
    (S : Scheme.{u}) (τ : StandardTopology)
    (M : @RingedSite.Hom.PullbackModel.{u, u + 1} _ _
      (Scheme.SiteRestriction.bigToZariski τ S) inferInstance inferInstance
      (modulePushforwardIsRightAdjointLifted S τ)) :
    (modulePullbackModel S τ).functor ≅ M.functor :=
  (modulePullbackModel S τ).iso M

/-- The pushforward model is canonically independent of a second explicit
right-derived model. -/
noncomputable def modulePushforwardModelIso
    (S : Scheme.{u}) (τ : StandardTopology)
    (M : CategoryTheory.Functor.RightDerived.Model
      (RingedSite.Hom.modulePushforwardToDerived.{u + 1}
        (Scheme.SiteRestriction.bigToZariski τ S))
      (RingedSite.Hom.moduleLocalization.{u + 1}
        (StandardTopology.Big.ringedSite τ S))
      (RingedSite.Hom.ModuleQis.{u + 1}
        (StandardTopology.Big.ringedSite τ S))) :
    (modulePushforwardModel S τ).functor ≅ M.functor :=
  (modulePushforwardModel S τ).iso M

/-- The specified pullback model carries its left-derived universal property. -/
theorem modulePullbackModelIsLeftDerived
    (S : Scheme.{u}) (τ : StandardTopology) :
    (modulePullbackModel S τ).functor.IsLeftDerivedFunctor
      (modulePullbackModel S τ).counit
      (RingedSite.Hom.ModuleQis.{u + 1}
        (Scheme.Zariski.Small.ringedSite S)) :=
  (modulePullbackModel S τ).isLeftDerived

/-- The specified pushforward model carries its right-derived universal property. -/
theorem modulePushforwardModelIsRightDerived
    (S : Scheme.{u}) (τ : StandardTopology) :
    (modulePushforwardModel S τ).functor.IsRightDerivedFunctor
      (modulePushforwardModel S τ).unit
      (RingedSite.Hom.ModuleQis.{u + 1}
        (StandardTopology.Big.ringedSite τ S)) :=
  (modulePushforwardModel S τ).isRightDerived

/-- The composite of the specified derived pullback and pushforward models
is an absolute left-derived functor. -/
theorem pullbackPushforwardModelIsLeftDerived
    (S : Scheme.{u}) (τ : StandardTopology) :
    ((modulePullbackModel S τ).functor ⋙
      (modulePushforwardModel S τ).functor).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (modulePullbackModel S τ).counit
          (modulePushforwardModel S τ).functor)
      (RingedSite.Hom.ModuleQis.{u + 1}
        (Scheme.Zariski.Small.ringedSite S)) := sorry

/-- The composite of the specified derived pushforward and pullback models
is an absolute right-derived functor. -/
theorem pushforwardPullbackModelIsRightDerived
    (S : Scheme.{u}) (τ : StandardTopology) :
    ((modulePushforwardModel S τ).functor ⋙
      (modulePullbackModel S τ).functor).IsRightDerivedFunctor
      (Functor.whiskerRight (modulePushforwardModel S τ).unit
          (modulePullbackModel S τ).functor ≫
        (Functor.associator _ _ _).hom)
      (RingedSite.Hom.ModuleQis.{u + 1}
        (StandardTopology.Big.ringedSite τ S)) := sorry

/-- The adjunction carried by the specified total-derived pullback and
pushforward models. -/
noncomputable def modelAdjunction
    (S : Scheme.{u}) (τ : StandardTopology) :
    (modulePullbackModel S τ).functor ⊣
      (modulePushforwardModel S τ).functor :=
  -- Local instance justification (proof-local temporary data): derived-category certificate for this adjunction.
  letI := bigSiteHasDerivedCategory S τ
  -- Local instance justification (proof-local temporary data): right-adjoint certificate for this adjunction.
  letI := modulePushforwardIsRightAdjointLifted S τ
  -- Local instance justification (proof-local temporary data): left-derived certificate for this adjunction.
  letI := modulePullbackHasLeftDerived S τ
  -- Local instance justification (proof-local temporary data): pullback model universal-property certificate.
  letI := modulePullbackModelIsLeftDerived S τ
  -- Local instance justification (proof-local temporary data): pushforward model universal-property certificate.
  letI := modulePushforwardModelIsRightDerived S τ
  -- Local instance justification (proof-local temporary data): pullback-pushforward derived certificate.
  letI := pullbackPushforwardModelIsLeftDerived S τ
  -- Local instance justification (proof-local temporary data): pushforward-pullback derived certificate.
  letI := pushforwardPullbackModelIsRightDerived S τ
  (Adjunction.mapHomotopyCategoryAdjunction
    ((Scheme.SiteRestriction.bigToZariski τ S
      ).modulePullbackPushforwardAdjunction.{u + 1})).derived
    (RingedSite.Hom.ModuleQis.{u + 1}
      (Scheme.Zariski.Small.ringedSite S))
    (RingedSite.Hom.ModuleQis.{u + 1}
      (StandardTopology.Big.ringedSite τ S))
    (modulePullbackModel S τ).counit
    (modulePushforwardModel S τ).unit

end AlgebraicGeometry.Scheme.SiteRestriction.bigToZariski

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- Quasi-coherent cohomology in the carrier-lifted, original-coefficient
small-Zariski derived category. -/
abbrev unliftedSmallZariskiProperty (S : Scheme.{u}) : ObjectProperty
    (RingedSite.Hom.ModuleDerived.{u + 1}
      (Scheme.Zariski.Small.ringedSite S)) :=
  (smallZariskiProperty S).map (smallRingDownDerived S)

/-- The carrier-lifted small-Zariski presentation of derived modules with
quasi-coherent cohomology. -/
abbrev UnliftedSmallZariski (S : Scheme.{u}) :=
  (unliftedSmallZariskiProperty S).FullSubcategory

/-- Forgetting the coefficient-ring lift preserves quasi-coherent
cohomology. -/
theorem smallRingDownDerived_mapsTo (S : Scheme.{u}) :
    smallZariskiProperty S ≤
      (unliftedSmallZariskiProperty S).inverseImage
        (smallRingDownDerived S) := sorry

/-- Restoring the lifted coefficient rings sends the transported
quasi-coherence property back to the canonical lifted property. -/
theorem smallRingUpDerived_mapsTo (S : Scheme.{u}) :
    unliftedSmallZariskiProperty S ≤
      (smallZariskiProperty S).inverseImage (smallRingUpDerived S) := sorry

/-- The restricted coefficient-ring comparison between the two
small-Zariski derived presentations. -/
noncomputable def smallRingDownRestricted (S : Scheme.{u}) :
    SmallZariski S ⥤ UnliftedSmallZariski S :=
  ObjectProperty.FullSubcategory.restrict
    (smallRingDownDerived S) (smallRingDownDerived_mapsTo S)

/-- The reverse restricted coefficient-ring comparison. -/
noncomputable def smallRingUpRestricted (S : Scheme.{u}) :
    UnliftedSmallZariski S ⥤ SmallZariski S :=
  ObjectProperty.FullSubcategory.restrict
    (smallRingUpDerived S) (smallRingUpDerived_mapsTo S)

/-- The derived coefficient-ring adjunction restricted to objects with
quasi-coherent cohomology. -/
noncomputable def smallRingRestrictedAdjunction (S : Scheme.{u}) :
    smallRingDownRestricted S ⊣ smallRingUpRestricted S :=
  ObjectProperty.FullSubcategory.adjunction _ _
    (smallRingDerivedAdjunction S)
    (smallRingDownDerived_mapsTo S) (smallRingUpDerived_mapsTo S)

/-- The coefficient-ring comparison is an equivalence on the
quasi-coherent-cohomology subcategories. -/
theorem smallRingDownRestrictedIsEquivalence (S : Scheme.{u}) :
    (smallRingDownRestricted S).IsEquivalence := sorry

/-- The canonical presentation of `Scheme.DerivedQCoh S` on the original
small-Zariski coefficient sheaf, with lifted module carriers. -/
noncomputable def smallPresentation (S : Scheme.{u}) :
    _root_.AlgebraicGeometry.Scheme.DerivedQCoh S ⥤ UnliftedSmallZariski S :=
  (smallZariskiEquivalence S).functor ⋙ smallRingDownRestricted S

/-- The inverse of the canonical original-coefficient small-Zariski
presentation. -/
noncomputable def fromSmallPresentation (S : Scheme.{u}) :
    UnliftedSmallZariski S ⥤
      _root_.AlgebraicGeometry.Scheme.DerivedQCoh S :=
  smallRingUpRestricted S ⋙ (smallZariskiEquivalence S).inverse

/-- The canonical and reverse original-coefficient small-Zariski
presentations form an adjunction. -/
noncomputable def smallPresentationAdjunction (S : Scheme.{u}) :
    smallPresentation S ⊣ fromSmallPresentation S :=
  (smallZariskiEquivalence S).toEquivalence.toAdjunction.comp
    (smallRingRestrictedAdjunction S)

end AlgebraicGeometry.Scheme.DerivedQCoh

namespace SheafOfModules.DerivedAdeq

variable (S : Scheme.{u}) (τ : StandardTopology)

/-- Derived pullback along the canonical morphism from the big `τ`-site to
the small Zariski site preserves adequate cohomology. -/
theorem smallAssociated_mapsTo :
    Scheme.DerivedQCoh.unliftedSmallZariskiProperty S ≤
      (SheafOfModules.derivedAdequateProperty S τ).inverseImage
        (Scheme.SiteRestriction.bigToZariski.modulePullbackModel S τ).functor := sorry

/-- Derived pushforward along the canonical morphism from the big `τ`-site
to the small Zariski site preserves quasi-coherent cohomology. -/
theorem smallZariskiRestriction_mapsTo :
    SheafOfModules.derivedAdequateProperty S τ ≤
      (Scheme.DerivedQCoh.unliftedSmallZariskiProperty S).inverseImage
        (Scheme.SiteRestriction.bigToZariski.modulePushforwardModel S τ).functor := sorry

/-- Derived pullback restricted from the carrier-lifted small-Zariski model
to complexes with adequate cohomology. -/
noncomputable def smallAssociated :
    Scheme.DerivedQCoh.UnliftedSmallZariski S ⥤ DerivedAdeq S τ :=
  ObjectProperty.FullSubcategory.restrict
    (Scheme.SiteRestriction.bigToZariski.modulePullbackModel S τ).functor
    (smallAssociated_mapsTo S τ)

/-- After forgetting the adequate-cohomology witness, `smallAssociated` is
the ambient total-derived pullback. -/
noncomputable def smallAssociated_inclusionIso :
    smallAssociated S τ ⋙ (SheafOfModules.derivedAdequateProperty S τ).ι ≅
      (Scheme.DerivedQCoh.unliftedSmallZariskiProperty S).ι ⋙
        (Scheme.SiteRestriction.bigToZariski.modulePullbackModel S τ).functor :=
  ObjectProperty.FullSubcategory.restrict.compιIso _
    (smallAssociated_mapsTo S τ)

/-- Derived pushforward restricted from adequate-cohomology complexes to the
carrier-lifted small-Zariski model. -/
noncomputable def smallZariskiRestriction :
    DerivedAdeq S τ ⥤ Scheme.DerivedQCoh.UnliftedSmallZariski S :=
  ObjectProperty.FullSubcategory.restrict
    (Scheme.SiteRestriction.bigToZariski.modulePushforwardModel S τ).functor
    (smallZariskiRestriction_mapsTo S τ)

/-- After forgetting the quasi-coherence witness,
`smallZariskiRestriction` is the ambient total-derived pushforward. -/
noncomputable def smallZariskiRestriction_inclusionIso :
    smallZariskiRestriction S τ ⋙
      (Scheme.DerivedQCoh.unliftedSmallZariskiProperty S).ι ≅
      (SheafOfModules.derivedAdequateProperty S τ).ι ⋙
        (Scheme.SiteRestriction.bigToZariski.modulePushforwardModel S τ).functor :=
  ObjectProperty.FullSubcategory.restrict.compιIso _
    (smallZariskiRestriction_mapsTo S τ)

/-- The restricted derived pullback and pushforward on the small-Zariski
presentation form an adjunction. -/
noncomputable def smallAdjunction :
    smallAssociated S τ ⊣ smallZariskiRestriction S τ :=
  ObjectProperty.FullSubcategory.adjunction _ _
    (Scheme.SiteRestriction.bigToZariski.modelAdjunction S τ)
    (smallAssociated_mapsTo S τ) (smallZariskiRestriction_mapsTo S τ)

/-- The derived association functor `Lf^*` from
`Scheme.DerivedQCoh S` to `DerivedAdeq S τ`. -/
noncomputable def associated :
    _root_.AlgebraicGeometry.Scheme.DerivedQCoh S ⥤ DerivedAdeq S τ :=
  Scheme.DerivedQCoh.smallPresentation S ⋙ smallAssociated S τ

/-- After passing through the original-coefficient small-Zariski
presentation, `associated` agrees with ambient total-derived pullback. -/
noncomputable def associated_inclusionIso :
    associated S τ ⋙ (SheafOfModules.derivedAdequateProperty S τ).ι ≅
      Scheme.DerivedQCoh.smallPresentation S ⋙
        ((Scheme.DerivedQCoh.unliftedSmallZariskiProperty S).ι ⋙
          (Scheme.SiteRestriction.bigToZariski.modulePullbackModel S τ).functor) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Scheme.DerivedQCoh.smallPresentation S)
      (smallAssociated_inclusionIso S τ)

/-- The derived Zariski-restriction functor `Rf_*` from
`DerivedAdeq S τ` to `Scheme.DerivedQCoh S`. -/
noncomputable def zariskiRestriction :
    DerivedAdeq S τ ⥤ _root_.AlgebraicGeometry.Scheme.DerivedQCoh S :=
  smallZariskiRestriction S τ ⋙
    Scheme.DerivedQCoh.fromSmallPresentation S

/-- After returning to the original-coefficient small-Zariski presentation,
`zariskiRestriction` maps canonically to ambient total-derived pushforward. -/
noncomputable def zariskiRestriction_inclusion :
    (zariskiRestriction S τ ⋙ Scheme.DerivedQCoh.smallPresentation S) ⋙
        (Scheme.DerivedQCoh.unliftedSmallZariskiProperty S).ι ⟶
      (SheafOfModules.derivedAdequateProperty S τ).ι ⋙
        (Scheme.SiteRestriction.bigToZariski.modulePushforwardModel S τ).functor :=
  (Functor.isoWhiskerRight
      (Functor.associator (smallZariskiRestriction S τ)
        (Scheme.DerivedQCoh.fromSmallPresentation S)
        (Scheme.DerivedQCoh.smallPresentation S))
      (Scheme.DerivedQCoh.unliftedSmallZariskiProperty S).ι).hom ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (smallZariskiRestriction S τ)
        (Scheme.DerivedQCoh.smallPresentationAdjunction S).counit)
      (Scheme.DerivedQCoh.unliftedSmallZariskiProperty S).ι ≫
    (Functor.isoWhiskerRight (Functor.rightUnitor (smallZariskiRestriction S τ))
      (Scheme.DerivedQCoh.unliftedSmallZariskiProperty S).ι).hom ≫
    (smallZariskiRestriction_inclusionIso S τ).hom

/-- The canonical comparison from `zariskiRestriction` to ambient
total-derived pushforward is invertible. -/
theorem zariskiRestriction_inclusionIsIso :
    IsIso (zariskiRestriction_inclusion S τ) := sorry

/-- Derived association is left adjoint to derived Zariski restriction. -/
noncomputable def adjunction : associated S τ ⊣ zariskiRestriction S τ :=
  (Scheme.DerivedQCoh.smallPresentationAdjunction S).comp
    (smallAdjunction S τ)

/-- The Hom equivalence of `adjunction` is the ambient total-derived Hom
equivalence followed by the small-presentation equivalence. -/
theorem adjunction_homEquiv_hom
    (K : _root_.AlgebraicGeometry.Scheme.DerivedQCoh S)
    (L : DerivedAdeq S τ) (f : (associated S τ).obj K ⟶ L) :
    (adjunction S τ).homEquiv K L f =
      (Scheme.DerivedQCoh.smallPresentationAdjunction S).homEquiv K
        ((smallZariskiRestriction S τ).obj L)
        (ObjectProperty.homMk
          ((Scheme.SiteRestriction.bigToZariski.modelAdjunction S τ).homEquiv
              ((Scheme.DerivedQCoh.smallPresentation S).obj K).obj L.obj
              ((associated_inclusionIso S τ).inv.app K ≫
                (SheafOfModules.derivedAdequateProperty S τ).ι.map f))) := sorry

/-- The unit of the derived association--restriction adjunction is an
isomorphism. -/
theorem adjunctionUnitIsIso : IsIso (adjunction S τ).unit := sorry

end SheafOfModules.DerivedAdeq
