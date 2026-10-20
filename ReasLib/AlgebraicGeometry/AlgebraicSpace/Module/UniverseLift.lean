module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Ring.ULift
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRing
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic

/-! # Universe lift and internal Hom of algebraic-space modules

The section carriers and restriction functions are the actual ULift construction.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open SheafOfModules.RingedSite

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace
variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- Abelian-group-valued weak sheafification exists on every slice of the small étale topology
in universe `u + 1`. -/
instance smallEtaleTopology_over_hasWeakSheafify_succ :
    ∀ U : smallEtaleSite X,
      HasWeakSheafify ((smallEtaleTopology X).over U) AddCommGrpCat.{u + 1} :=
  sorry

/-- On every slice of the small étale topology, sheafification equivalences in universe `u + 1`
are the locally bijective morphisms. -/
instance smallEtaleTopology_over_wEqualsLocallyBijective_succ :
    ∀ U : smallEtaleSite X,
      ((smallEtaleTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  sorry

/-- Abelian-group-valued weak sheafification exists on every double slice of the small étale
topology in universe `u + 1`. -/
instance smallEtaleTopology_over_over_hasWeakSheafify_succ :
    ∀ (U : smallEtaleSite X) (V : Over U),
      HasWeakSheafify (((smallEtaleTopology X).over U).over V) AddCommGrpCat.{u + 1} :=
  sorry

/-- On every double slice of the small étale topology, sheafification equivalences in universe
`u + 1` are the locally bijective morphisms. -/
instance smallEtaleTopology_over_over_wEqualsLocallyBijective_succ :
    ∀ (U : smallEtaleSite X) (V : Over U),
      (((smallEtaleTopology X).over U).over V).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Modules
variable {S : Scheme.{u}} (X : AlgebraicSpace S)

variable {X}

/-- Universe lift of the value of a commutative module sheaf at `U`. -/
noncomputable def liftedSection (F : commModules X) (U : (smallEtaleSite X)ᵒᵖ) :
    ModuleCat.{u + 1} ((commStructureSheafLift X).obj.obj U) :=
  (ModuleCat.restrictScalars (ULift.ringEquiv.{u, u + 1}).toRingHom).obj
    ((ModuleCat.uliftFunctor.{u + 1, u} ((commStructureSheaf X).obj.obj U)).obj
      (F.val.obj U))

/-- `liftedSection F U` is restriction of scalars of the universe lift of `F(U)`. -/
theorem liftedSection_eq (F : commModules X) (U : (smallEtaleSite X)ᵒᵖ) :
    liftedSection F U =
      (ModuleCat.restrictScalars (ULift.ringEquiv.{u, u + 1}).toRingHom).obj
        ((ModuleCat.uliftFunctor.{u + 1, u} ((commStructureSheaf X).obj.obj U)).obj
          (F.val.obj U)) :=
  rfl

/-- Target of a lifted restriction map. -/
abbrev liftedSectionRestrictTarget (F : commModules X)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :=
  (ModuleCat.restrictScalars ((commStructureSheafLift X).obj.map i).hom).obj
    (liftedSection F V)

/-- Restriction of a universe-lifted module of sections. -/
noncomputable def liftedSectionRestrict (F : commModules X)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :
    liftedSection F U ⟶ liftedSectionRestrictTarget F i :=
  ModuleCat.ofHom
    (X := liftedSection F U)
    (Y := liftedSectionRestrictTarget F i)
    { toFun := fun x ↦ ULift.up (F.val.map i x.down)
      map_add' := sorry
      map_smul' := sorry }

/-- Applying lifted restriction recovers `ULift` of restriction of sections. -/
theorem liftedSectionRestrict_apply (F : commModules X) {U V : (smallEtaleSite X)ᵒᵖ}
    (i : U ⟶ V) (x : liftedSection F U) :
    liftedSectionRestrict F i x = ULift.up (F.val.map i x.down) :=
  sorry

/-- Universe lift of a commutative module presheaf to `CommRingCat.{u + 1}`. -/
noncomputable def liftedPresheaf (F : commModules X) :
    PresheafOfModules.{u + 1}
      (ringSheaf.{u + 1, u, u + 1} (smallEtaleTopology X)
        (commStructureSheafLift X)).obj where
  obj U := liftedSection F U
  map i := liftedSectionRestrict F i
  map_id := sorry
  map_comp := sorry

/-- The universe-lifted presheaf evaluates by `liftedSection`. -/
theorem liftedPresheaf_obj (F : commModules X) (U : (smallEtaleSite X)ᵒᵖ) :
    (liftedPresheaf F).obj U = liftedSection F U :=
  rfl

/-- The universe-lifted presheaf of a commutative module sheaf is a sheaf. -/
theorem liftedPresheaf_isSheaf (F : commModules X) :
    Presheaf.IsSheaf (smallEtaleTopology X) (liftedPresheaf F).presheaf :=
  sorry

/-- Universe lift of a commutative `𝒪_X`-module to the `CommRingCat.{u + 1}` presentation. -/
noncomputable def liftCommModule (F : commModules X) :
    RingedSite.ModuleCat.{u + 1} (commRingedSiteLift X) where
  val := liftedPresheaf F
  isSheaf := liftedPresheaf_isSheaf F

/-- The underlying presheaf of `liftCommModule F` is `liftedPresheaf F`. -/
theorem liftCommModule_val (F : commModules X) :
    (liftCommModule F).val = liftedPresheaf F :=
  rfl

/-- Universe lift of an `𝒪_X`-module to the `CommRingCat.{u + 1}` presentation. -/
noncomputable def liftModule (F : X.Modules) :
    RingedSite.ModuleCat.{u + 1} (commRingedSiteLift X) :=
  liftCommModule ((toCommModules X).obj F)

/-- The universe lift of an `𝒪_X`-module evaluates by lifting the commutative presentation. -/
theorem liftModule_val (F : X.Modules) :
    liftModule F = liftCommModule ((toCommModules X).obj F) :=
  rfl

/-- The internal Hom of two `𝒪_X`-modules, with sections over `U` equal to morphisms
`F|U ⟶ G|U` on the universe-lifted commutative presentation. -/
noncomputable def internalHom (F G : X.Modules) :
    RingedSite.ModuleCat.{u + 1} (commRingedSiteLift X) :=
  SheafOfModules.RingedSite.InternalHom.obj.{u + 1, u, u + 1}
    (commStructureSheafLift X) (liftModule F) (liftModule G)

/-- Sections of `internalHom F G` over `U` are morphisms between the restrictions of the
universe-lifted modules to the slice over `U`. -/
theorem internalHom_val_obj (F G : X.Modules) (U : (smallEtaleSite X)ᵒᵖ) :
    (internalHom F G).val.obj U =
      ModuleCat.of ((commStructureSheafLift X).obj.obj U)
        (SheafOfModules.RingedSite.InternalHom.LocalHom.{u + 1, u, u + 1}
          (commStructureSheafLift X) (liftModule F) (liftModule G) U) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
