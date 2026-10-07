module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.Logic.Small.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import stacks_project.Chap96.Lemma_96_12_2
public import stacks_project.Chap96.Lemma_96_12_3_Pullback
public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap103.Definition_103_7_1_FlatBaseChange
public import stacks_project.Chap103.«103_15_1_1_Smooth»

/-!
# Lemma 103.7.2

On an algebraic stack, the étale modules with the flat base change property are
stable under pullback, form a weak Serre class, descend along jointly
point-covering smooth families, are closed under colimits, and are closed under
tensor and under internal Hom from a finitely presented étale module.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.MonoidalClosed CategoryTheory.ObjectProperty
  SheafOfModules.RingedSite.InternalHom
open scoped SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Lemma 103.7.2 (1): if `F` is an étale `𝒪_X`-module with the flat base change
property and `g : Y ⟶ X` is a morphism of algebraic stacks, then the pullback
`g^* F` has the flat base change property. -/
@[stacks 0764]
instance instHasFlatBaseChange_pullback
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (g : Y ⟶ X) (F : etaleModules X) [HasFlatBaseChange F] :
    HasFlatBaseChange ((moduleInverseImage g).obj F) :=
  sorry

/-- Lemma 103.7.2 (2): étale `𝒪_X`-modules with the flat base change property
form a weak Serre subcategory of `Mod(X_étale, 𝒪_X)`. -/
@[stacks 0764]
instance instHasFlatBaseChange_isWeakSerreClass
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (hasFlatBaseChange X).IsWeakSerreClass :=
  sorry

/-- The inclusion of étale modules with the flat base change property is exact. -/
theorem hasFlatBaseChange_inclusion_exact
    (X : GroupoidsOver S) [AlgebraicStack X] :
    exactFunctor (hasFlatBaseChange X).FullSubcategory (etaleModules X)
      (hasFlatBaseChange X).ι :=
  sorry

/-- Lemma 103.7.2 (3): if `f i : Xi i ⟶ X` is a family of smooth morphisms of
algebraic stacks covering `|X|` and each pullback `(f i)^* F` has the flat
base change property, then so does `F`. -/
@[stacks 0764]
theorem hasFlatBaseChange_of_smoothCovering
    {X : GroupoidsOver S} [AlgebraicStack X] {ι : Type v}
    {Xi : ι → GroupoidsOver S} [∀ i, AlgebraicStack (Xi i)]
    (f : ∀ i, Xi i ⟶ X) [∀ i, AlgebraicStack.Smooth (f i)]
    (h_cover : ∀ x : AlgebraicStack.Points X,
      ∃ i, x ∈ Set.range (AlgebraicStack.Points.map (f i)))
    (F : etaleModules X)
    (hF : ∀ i, HasFlatBaseChange ((moduleInverseImage (f i)).obj F)) :
    HasFlatBaseChange F :=
  sorry

/-- Lemma 103.7.2 (4): étale `𝒪_X`-modules with the flat base change property
are closed under colimits in `Mod(X_étale, 𝒪_X)`. -/
@[stacks 0764]
instance instHasFlatBaseChange_isClosedUnderColimitsOfShape
    (X : GroupoidsOver S) [AlgebraicStack X] (J : Type v) [Category.{w} J] :
    (hasFlatBaseChange X).IsClosedUnderColimitsOfShape J :=
  sorry

/-- The inclusion of étale modules with the flat base change property creates
colimits of every universe-compatible shape. -/
instance instHasFlatBaseChange_createsColimitsOfShape
    (X : GroupoidsOver S) [AlgebraicStack X] (J : Type v) [Category.{w} J] :
    CreatesColimitsOfShape J (hasFlatBaseChange X).ι :=
  createsColimitsOfShapeFullSubcategoryInclusion J (hasFlatBaseChange X)

/-- Colimits of étale modules with the flat base change property agree with
colimits computed in `Mod(X_étale, 𝒪_X)`. -/
def hasFlatBaseChange_inclusion_colimitIso
    {X : GroupoidsOver S} [AlgebraicStack X] {J : Type v} [Category.{w} J]
    (F : J ⥤ (hasFlatBaseChange X).FullSubcategory)
    [HasColimit F] [HasColimit (F ⋙ (hasFlatBaseChange X).ι)]
    [PreservesColimit F (hasFlatBaseChange X).ι] :
    colimit (F ⋙ (hasFlatBaseChange X).ι) ≅
      ((hasFlatBaseChange X).ι).obj (colimit F) :=
  (preservesColimitIso (hasFlatBaseChange X).ι F).symm

/-- `hasFlatBaseChange_inclusion_colimitIso` is the inverse of the canonical
`preservesColimitIso`. -/
theorem hasFlatBaseChange_inclusion_colimitIso_eq
    {X : GroupoidsOver S} [AlgebraicStack X] {J : Type v} [Category.{w} J]
    (F : J ⥤ (hasFlatBaseChange X).FullSubcategory)
    [HasColimit F] [HasColimit (F ⋙ (hasFlatBaseChange X).ι)]
    [PreservesColimit F (hasFlatBaseChange X).ι] :
    hasFlatBaseChange_inclusion_colimitIso F =
      (preservesColimitIso (hasFlatBaseChange X).ι F).symm :=
  sorry

/-- Lemma 103.7.2 (5): the tensor product of two étale `𝒪_X`-modules with the
flat base change property again has the flat base change property. -/
@[stacks 0764]
instance instHasFlatBaseChange_tensor {X : GroupoidsOver S} [AlgebraicStack X]
    (F G : etaleModules X) [HasFlatBaseChange F] [HasFlatBaseChange G] :
    HasFlatBaseChange (moduleTensorEtale F G) :=
  sorry

/-- Universe lift of an étale `𝒪_X`-module to the commutative lifted étale
ringed site. -/
def liftEtaleModule {X : GroupoidsOver S} (F : etaleModules X) :
    RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X) where
  val :=
    { obj U :=
        (ModuleCat.restrictScalars (ULift.ringEquiv.{u, u + 1}).toRingHom).obj
          ((ModuleCat.uliftFunctor.{u + 1, u}
              ((etaleRingedSite X).structureSheaf.obj.obj U)).obj
            (F.val.obj U))
      map i :=
        (ModuleCat.restrictScalars (ULift.ringEquiv.{u, u + 1}).toRingHom).map
          ((ModuleCat.uliftFunctor.{u + 1, u}
              ((etaleRingedSite X).structureSheaf.obj.obj _)).map
            (F.val.map i))
      map_id := sorry
      map_comp := sorry }
  isSheaf := sorry

/-- Sections of `liftEtaleModule F` are universe lifts of the sections of `F`,
with scalars restricted along `ULift.ringEquiv`. -/
theorem liftEtaleModule_val_obj {X : GroupoidsOver S} (F : etaleModules X)
    (U : X.totalᵒᵖ) :
    (liftEtaleModule F).val.obj U =
      (ModuleCat.restrictScalars (ULift.ringEquiv.{u, u + 1}).toRingHom).obj
        ((ModuleCat.uliftFunctor.{u + 1, u}
            ((etaleRingedSite X).structureSheaf.obj.obj U)).obj
          (F.val.obj U)) :=
  rfl

/-- Universe-`u` sections of a lift of a universe-`u` étale module are `u`-small. -/
instance liftEtaleModule_small {X : GroupoidsOver S} (F : etaleModules X)
    (U : X.totalᵒᵖ) :
    Small.{u} ((liftEtaleModule F).val.obj U) :=
  Small.mk' Equiv.ulift.{u + 1, u}

/-- Restriction of scalars preserves the underlying type, hence preserves
`Small.{u}`. -/
instance etaleRestrictScalars_small.{r, s} {R : Type r} {S : Type s} [Ring R]
    [Ring S] (f : R →+* S) (N : ModuleCat.{u + 1} S) [h : Small.{u} N] :
    Small.{u} ((ModuleCat.restrictScalars.{u + 1} f).obj N) :=
  h

/-- Down-universe of a module in universe `u + 1` with `u`-small carrier. -/
def etaleModuleCatDown (R : Type u) [Ring R] (N : ModuleCat.{u + 1} R)
    [Small.{u} N] : ModuleCat.{u} R :=
  ModuleCat.of R (Shrink.{u} (N : Type (u + 1)))

/-- `etaleModuleCatDown` is `ModuleCat.of` of the `u`-shrink of the carrier. -/
theorem etaleModuleCatDown_eq (R : Type u) [Ring R] (N : ModuleCat.{u + 1} R)
    [Small.{u} N] :
    etaleModuleCatDown R N = ModuleCat.of R (Shrink.{u} (N : Type (u + 1))) :=
  rfl

/-- A morphism of small modules down-transports by conjugating with `equivShrink`. -/
def etaleModuleCatDownMap {R : Type u} [Ring R] {N N' : ModuleCat.{u + 1} R}
    [Small.{u} N] [Small.{u} N'] (f : N ⟶ N') :
    etaleModuleCatDown R N ⟶ etaleModuleCatDown R N' :=
  ModuleCat.ofHom
    { toFun := fun x ↦
        equivShrink (N' : Type (u + 1))
          (f.hom ((equivShrink (N : Type (u + 1))).symm x))
      map_add' := sorry
      map_smul' := sorry }

/-- Applying `etaleModuleCatDownMap` conjugates the underlying linear map by
`equivShrink`. -/
theorem etaleModuleCatDownMap_apply {R : Type u} [Ring R]
    {N N' : ModuleCat.{u + 1} R} [Small.{u} N] [Small.{u} N']
    (f : N ⟶ N') (x : etaleModuleCatDown R N) :
    etaleModuleCatDownMap f x =
      equivShrink (N' : Type (u + 1))
        (f.hom ((equivShrink (N : Type (u + 1))).symm x)) :=
  sorry

/-- Inverse of `liftEtaleModule` on one lifted module: restrict scalars along
`ULift.ringEquiv.symm`, then down-universe the carrier. -/
def fromLiftedEtaleModule {X : GroupoidsOver S}
    (M : RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X))
    [∀ U, Small.{u} (M.val.obj U)] : etaleModules X where
  val :=
    { obj U :=
        etaleModuleCatDown ((commEtaleStructureSheaf X).obj.obj U)
          ((ModuleCat.restrictScalars
              (ULift.ringEquiv.{u, u + 1}.symm).toRingHom).obj
            (M.val.obj U))
      map {U V} i :=
        eqToHom sorry ≫
          etaleModuleCatDownMap
            ((ModuleCat.restrictScalars
                (ULift.ringEquiv.{u, u + 1}.symm).toRingHom).map
              (M.val.map i)) ≫
          eqToHom sorry
      map_id := sorry
      map_comp := sorry }
  isSheaf := sorry

/-- The object action of `fromLiftedEtaleModule` is restriction of scalars along
`ULift.ringEquiv.symm` followed by down-universe of the carrier. -/
theorem fromLiftedEtaleModule_val_obj {X : GroupoidsOver S}
    (M : RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X))
    [∀ U, Small.{u} (M.val.obj U)] (U : X.totalᵒᵖ) :
    (fromLiftedEtaleModule M).val.obj U =
      etaleModuleCatDown ((commEtaleStructureSheaf X).obj.obj U)
        ((ModuleCat.restrictScalars
            (ULift.ringEquiv.{u, u + 1}.symm).toRingHom).obj
          (M.val.obj U)) :=
  rfl

/-- The canonical sheaf Hom of two étale modules, computed as internal Hom on
the universe-lifted commutative étale module category. -/
def liftedEtaleSheafHom {X : GroupoidsOver S} (F G : etaleModules X) :
    RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X) :=
  (ihom (liftEtaleModule F)).obj (liftEtaleModule G)

/-- `liftedEtaleSheafHom` is the monoidal internal Hom of the universe lifts. -/
theorem liftedEtaleSheafHom_eq {X : GroupoidsOver S} (F G : etaleModules X) :
    liftedEtaleSheafHom F G =
      (ihom (liftEtaleModule F)).obj (liftEtaleModule G) :=
  rfl

/-- Sections of lifted sheaf Hom over `U` are morphisms between the restrictions
of the universe-lifted modules to the slice over `U`. -/
theorem liftedEtaleSheafHom_val_obj {X : GroupoidsOver S}
    (F G : etaleModules X) (U : X.totalᵒᵖ) :
    (liftedEtaleSheafHom F G).val.obj U =
      ModuleCat.of ((commEtaleStructureSheafLift X).obj.obj U)
        (LocalHom.{u + 1, u, u + 1}
          (commEtaleStructureSheafLift X)
          (liftEtaleModule F) (liftEtaleModule G) U) :=
  sorry

/-- Sections of lifted sheaf Hom from a finitely presented étale module are
`u`-small. -/
instance liftedEtaleSheafHom_small {X : GroupoidsOver S}
    (F G : etaleModules X) [F.IsFinitePresentation] (U : X.totalᵒᵖ) :
    Small.{u} ((liftedEtaleSheafHom F G).val.obj U) :=
  sorry

/-- The sheaf Hom `SheafHom_{𝒪_X}(F, G)` of étale `𝒪_X`-modules, obtained by
down-transporting the lifted internal Hom. -/
def moduleSheafHomEtale {X : GroupoidsOver S} (F G : etaleModules X)
    [F.IsFinitePresentation] : etaleModules X :=
  fromLiftedEtaleModule (liftedEtaleSheafHom F G)

/-- `moduleSheafHomEtale` is the down-transport of `liftedEtaleSheafHom`. -/
theorem moduleSheafHomEtale_eq {X : GroupoidsOver S} (F G : etaleModules X)
    [F.IsFinitePresentation] :
    moduleSheafHomEtale F G =
      fromLiftedEtaleModule (liftedEtaleSheafHom F G) :=
  rfl

/-- A function between `ModuleCat` objects, promoted to a morphism with linearity
deferred. -/
def etaleModuleCatOfFun {R : Type (u + 1)} [Ring R]
    (src tgt : ModuleCat.{u + 1} R) (f : src → tgt) : src ⟶ tgt :=
  ModuleCat.ofHom
    { toFun := f
      map_add' := sorry
      map_smul' := sorry }

/-- `etaleModuleCatOfFun` applies the supplied function. -/
theorem etaleModuleCatOfFun_apply {R : Type (u + 1)} [Ring R]
    (src tgt : ModuleCat.{u + 1} R) (f : src → tgt) (x : src) :
    etaleModuleCatOfFun src tgt f x = f x :=
  sorry

/-- Forward component of the lift-down round trip, given by `ULift.down` and
`equivShrink.symm` after restriction of scalars along `ULift.ringEquiv`. -/
def fromLiftedEtaleModule_isoHomApp {X : GroupoidsOver S}
    (M : RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X))
    [∀ U, Small.{u} (M.val.obj U)] (U : X.totalᵒᵖ) :
    (liftEtaleModule (fromLiftedEtaleModule M)).val.obj U ⟶ M.val.obj U :=
  etaleModuleCatOfFun
    ((liftEtaleModule (fromLiftedEtaleModule M)).val.obj U) (M.val.obj U)
    (fun x ↦ (equivShrink (M.val.obj U : Type (u + 1))).symm (ULift.down x))

/-- Inverse component of the lift-down round trip, given by `equivShrink` and
`ULift.up` after restriction of scalars along `ULift.ringEquiv`. -/
def fromLiftedEtaleModule_isoInvApp {X : GroupoidsOver S}
    (M : RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X))
    [∀ U, Small.{u} (M.val.obj U)] (U : X.totalᵒᵖ) :
    M.val.obj U ⟶ (liftEtaleModule (fromLiftedEtaleModule M)).val.obj U :=
  etaleModuleCatOfFun
    (M.val.obj U) ((liftEtaleModule (fromLiftedEtaleModule M)).val.obj U)
    (fun y ↦ ULift.up (equivShrink (M.val.obj U : Type (u + 1)) y))

/-- Applying `fromLiftedEtaleModule_isoHomApp` is `equivShrink.symm` after
`ULift.down`. -/
theorem fromLiftedEtaleModule_isoHomApp_apply {X : GroupoidsOver S}
    (M : RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X))
    [∀ U, Small.{u} (M.val.obj U)] (U : X.totalᵒᵖ)
    (x : (liftEtaleModule (fromLiftedEtaleModule M)).val.obj U) :
    fromLiftedEtaleModule_isoHomApp M U x =
      (equivShrink (M.val.obj U : Type (u + 1))).symm (ULift.down x) :=
  sorry

/-- Applying `fromLiftedEtaleModule_isoInvApp` is `ULift.up` after
`equivShrink`. -/
theorem fromLiftedEtaleModule_isoInvApp_apply {X : GroupoidsOver S}
    (M : RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X))
    [∀ U, Small.{u} (M.val.obj U)] (U : X.totalᵒᵖ) (y : M.val.obj U) :
    fromLiftedEtaleModule_isoInvApp M U y =
      ULift.up (equivShrink (M.val.obj U : Type (u + 1)) y) :=
  sorry

/-- The lift of the down-transport of a lifted étale module is canonically
isomorphic to the original lifted module. The components are the linear
equivalences of `ULift.ringEquiv` and `equivShrink`. -/
def fromLiftedEtaleModule_iso {X : GroupoidsOver S}
    (M : RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X))
    [∀ U, Small.{u} (M.val.obj U)] :
    liftEtaleModule (fromLiftedEtaleModule M) ≅ M where
  hom := { val := { app := fromLiftedEtaleModule_isoHomApp M, naturality := sorry } }
  inv := { val := { app := fromLiftedEtaleModule_isoInvApp M, naturality := sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward component of `fromLiftedEtaleModule_iso` is
`fromLiftedEtaleModule_isoHomApp`. -/
theorem fromLiftedEtaleModule_iso_hom_app {X : GroupoidsOver S}
    (M : RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X))
    [∀ U, Small.{u} (M.val.obj U)] (U : X.totalᵒᵖ) :
    (fromLiftedEtaleModule_iso M).hom.val.app U =
      fromLiftedEtaleModule_isoHomApp M U :=
  rfl

/-- The universe lift of `moduleSheafHomEtale F G` is canonically isomorphic to
the lifted sheaf Hom `SheafHom_{𝒪_X}(F, G)`, via `ULift.ringEquiv` and
`equivShrink`. -/
def moduleSheafHomEtale_spec {X : GroupoidsOver S} (F G : etaleModules X)
    [F.IsFinitePresentation] :
    liftEtaleModule (moduleSheafHomEtale F G) ≅ liftedEtaleSheafHom F G :=
  fromLiftedEtaleModule_iso (liftedEtaleSheafHom F G)

/-- `moduleSheafHomEtale_spec` is the lift-down round-trip isomorphism of
`liftedEtaleSheafHom`. -/
theorem moduleSheafHomEtale_spec_eq {X : GroupoidsOver S} (F G : etaleModules X)
    [F.IsFinitePresentation] :
    moduleSheafHomEtale_spec F G =
      fromLiftedEtaleModule_iso (liftedEtaleSheafHom F G) :=
  rfl

/-- Lemma 103.7.2 (6): sheaf Hom from a finitely presented étale `𝒪_X`-module
into an étale module with the flat base change property again has the flat
base change property. -/
@[stacks 0764]
instance instHasFlatBaseChange_sheafHom {X : GroupoidsOver S} [AlgebraicStack X]
    (F G : etaleModules X) [F.IsFinitePresentation] [HasFlatBaseChange G] :
    HasFlatBaseChange (moduleSheafHomEtale F G) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
