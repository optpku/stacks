/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module.Restriction
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids.Hom
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module.SpacePushforward
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Adjunction
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.RepresentedSections
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import ReasLib.CategoryTheory.Sites.Topos.InternalModule

/-!
# Algebraic-space comparison morphisms of étale modules

A 2-commutative triangle of groupoid fibrations with algebraic-space
presentations gives a comparison between small étale module pullback and
restriction of inverse image. The comparison is the mate of the restricted
unit, transported along the given 2-isomorphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Functor Opposite
open FiberedCategoryOver.Groupoids
open RingedSite.Hom
open CategoryTheory.Limits
open CategoryTheory.Sheaf.InternalModule
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Evaluation of a restricted CFG module at `W` recovers sections at `u_V(W)`. -/
def restrictDirectImageComparison_leftEval {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {V : AlgebraicSpace S}
    [HasSmallCFGTypeSections (S := S) a]
    (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite V) :
    ((ToInternal.underlying (AlgebraicSpace.structureSheaf V)).obj
        ((restrictModules eV).obj ((etaleModuleDirectImage a).obj H))).obj.obj (op W) ≅
      ((ToInternal.underlying (etaleRingedSite Vcfg).structureSheaf).obj
        ((etaleModuleDirectImage a).obj H)).obj.obj
          (op ((smallEtaleFunctor V Vcfg eV).obj W)) :=
  Iso.refl _

/-- The comma category computing CFG pushforward at `u_V(W)`. -/
abbrev restrictDirectImageComparison_bigIndex {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {V : AlgebraicSpace S} (eV : V.toGroupoids ≌ Vcfg)
    (W : AlgebraicSpace.smallEtaleSite V) :=
  StructuredArrow (op ((smallEtaleFunctor V Vcfg eV).obj W))
    (toCartesianBasedFunctor a).toFunctor.op

/-- The comma category computing small étale pushforward at `W ×_V U`. -/
abbrev restrictDirectImageComparison_smallIndex {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (W : AlgebraicSpace.smallEtaleSite V) :=
  AlgebraicSpace.compareSmallIndex (moduleComparisonSpaceMorphism a eU eV) W

/-- Kan diagram for CFG pushforward of the underlying sheaf at `u_V(W)`. -/
abbrev restrictDirectImageComparison_bigDiag {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {V : AlgebraicSpace S} (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite V) :
    restrictDirectImageComparison_bigIndex a eV W ⥤ Type u :=
  StructuredArrow.proj (op ((smallEtaleFunctor V Vcfg eV).obj W))
      (toCartesianBasedFunctor a).toFunctor.op ⋙
    ((ToInternal.underlying (etaleRingedSite Ucfg).structureSheaf).obj H).obj

/-- Kan diagram for small étale pushforward of the restricted underlying sheaf. -/
abbrev restrictDirectImageComparison_smallDiag {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite V) :
    restrictDirectImageComparison_smallIndex a eU eV W ⥤ Type u :=
  StructuredArrow.proj
      (op ((AlgebraicSpace.etaleBaseChange
          (moduleComparisonSpaceMorphism a eU eV)).obj W))
      (AlgebraicGeometry.AlgebraicSpace.smallEtaleToSpaces U).op ⋙
    ((ToInternal.underlying (AlgebraicSpace.structureSheaf U)).obj
      ((restrictModules eU).obj H)).obj

set_option backward.isDefEq.respectTransparency false in
private theorem restrictDirectImageComparison_evalTransport {U V : AlgebraicSpace S}
    (ψ : U.toGroupoids ⟶ V.toGroupoids) (x : U.toGroupoids.total) :
    V.functorOfPoints.map (((eqToIso (comm ψ)).app x).hom.op)
        ((AlgebraicSpace.toGroupoids.eval ψ).app (op (U.toGroupoids.p.obj x)) x.unop.2) =
      ((toFunctor ψ).obj x).unop.2 := by
  rcases x with ⟨⟨T, t⟩⟩
  change V.functorOfPoints.map _ (V.functorOfPoints.map _ _) = _
  rw [← Functor.map_comp_apply]
  simp only [FiberedCategoryOver.Groupoids.fiberFunctor, BasedFunctor.fiberFunctor,
    Functor.Fiber.inducedFunctor, FiberedCategoryOver.Sets.ofPresheaf.valueToFiber]
  simp [eqToHom_app]
  rfl

private theorem restrictDirectImageComparison_compareOverHom_section
    {U V : AlgebraicSpace S} (f : U ⟶ V)
    (W : AlgebraicSpace.smallEtaleSite V) (k : AlgebraicSpace.compareSmallIndex f W) :
    V.functorOfPoints.map (AlgebraicSpace.compareOverHom f k).op (yonedaEquiv W.hom) =
      f.app (op k.right.unop.left) (yonedaEquiv k.right.unop.hom) := by
  rw [yonedaEquiv_naturality, ← yonedaEquiv_comp]
  apply congrArg yonedaEquiv
  rw [show yoneda.map (AlgebraicSpace.compareOverHom f k) =
      AlgebraicSpace.compareSmallToBaseChange f k ≫ AlgebraicSpace.etaleBaseChangeSnd f W from
    yonedaEquiv.symm_apply_apply _]
  have hpb : AlgebraicSpace.etaleBaseChangeSnd f W ≫ W.hom =
      AlgebraicSpace.etaleBaseChangeHom f W ≫ f :=
    (pullback.condition (f := AlgebraicSpace.homFunctor f)
      (g := AlgebraicSpace.homFunctor W.hom)).symm
  calc
    (AlgebraicSpace.compareSmallToBaseChange f k ≫
          AlgebraicSpace.etaleBaseChangeSnd f W) ≫ W.hom =
        AlgebraicSpace.compareSmallToBaseChange f k ≫
          (AlgebraicSpace.etaleBaseChangeSnd f W ≫ W.hom) := Category.assoc _ _ _
    _ = AlgebraicSpace.compareSmallToBaseChange f k ≫
        (AlgebraicSpace.etaleBaseChangeHom f W ≫ f) := congrArg _ hpb
    _ = (AlgebraicSpace.compareSmallToBaseChange f k ≫
        AlgebraicSpace.etaleBaseChangeHom f W) ≫ f := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun t => t ≫ f) k.hom.unop.w

/-- The morphism `a(u_U(T')) ⟶ u_V(W)` in `Vcfg`, obtained by transporting the
identity-presentation comparison morphism along `eV`. -/
def restrictDirectImageComparison_indexHom {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (W : AlgebraicSpace.smallEtaleSite V)
    (k : restrictDirectImageComparison_smallIndex a eU eV W) :
    (toCartesianBasedFunctor a).toFunctor.obj
        ((smallEtaleFunctor U Ucfg eU).obj k.right.unop) ⟶
      (smallEtaleFunctor V Vcfg eV).obj W :=
  let x := (smallEtaleToGroupoids U).obj k.right.unop
  let z := (smallEtaleToGroupoids V).obj W
  let ψ := RepresentedDirectImage.presentedMorphism a eU eV
  let β : (toFunctor ψ).obj x ⟶ z :=
    (CategoryOfElements.homMk (unop z) (unop ((toFunctor ψ).obj x))
      (((eqToIso (comm ψ)).app x).hom ≫
        AlgebraicSpace.compareOverHom (moduleComparisonSpaceMorphism a eU eV) k).op
      (by
        calc
          _ = V.functorOfPoints.map (((eqToIso (comm ψ)).app x).hom.op)
              (V.functorOfPoints.map
                (AlgebraicSpace.compareOverHom (moduleComparisonSpaceMorphism a eU eV) k).op
                z.unop.2) := V.functorOfPoints.map_comp_apply _ _ _
          _ = V.functorOfPoints.map (((eqToIso (comm ψ)).app x).hom.op)
              ((AlgebraicSpace.toGroupoids.eval ψ).app (op (U.toGroupoids.p.obj x))
                x.unop.2) := congrArg _
                  (restrictDirectImageComparison_compareOverHom_section
                    (moduleComparisonSpaceMorphism a eU eV) W k)
          _ = _ := restrictDirectImageComparison_evalTransport ψ x)).op
  (eqToIso (cartesian_toFunctor_eq a)).hom.app ((toFunctor eU.hom).obj x) ≫
    (RepresentedDirectImage.targetCounitIso eV).inv.app _ ≫
    (toFunctor eV.hom).map
      ((toFunctor eV.inv).map
          ((ObjectProperty.FullSubbicategory.toFunctor.compIso eU.hom a).hom.app x) ≫
        (ObjectProperty.FullSubbicategory.toFunctor.compIso (eU.hom ≫ a) eV.inv).hom.app x ≫
        β)

/-- Opposite form of `restrictDirectImageComparison_indexHom`, as a structured arrow. -/
def restrictDirectImageComparison_indexArrow {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (W : AlgebraicSpace.smallEtaleSite V)
    (k : restrictDirectImageComparison_smallIndex a eU eV W) :
    op ((smallEtaleFunctor V Vcfg eV).obj W) ⟶
      (toCartesianBasedFunctor a).toFunctor.op.obj
        (op ((smallEtaleFunctor U Ucfg eU).obj k.right.unop)) :=
  (restrictDirectImageComparison_indexHom a eU eV W k).op

set_option backward.isDefEq.respectTransparency false in
private theorem restrictDirectImageComparison_compareOverHom_naturality
    {U V : AlgebraicSpace S} (f : U ⟶ V) (W : AlgebraicSpace.smallEtaleSite V)
    {k k' : AlgebraicSpace.compareSmallIndex f W} (α : k ⟶ k') :
    α.right.unop.left ≫ AlgebraicSpace.compareOverHom f k =
      AlgebraicSpace.compareOverHom f k' := by
  have hα : AlgebraicSpace.ofOverMap α.right.unop.left ≫ k.hom.unop.left =
      k'.hom.unop.left := congrArg (fun t => t.unop.left) α.w
  apply yoneda.map_injective
  calc
    yoneda.map (α.right.unop.left ≫ AlgebraicSpace.compareOverHom f k) =
        yoneda.map α.right.unop.left ≫ yoneda.map (AlgebraicSpace.compareOverHom f k) :=
      yoneda.map_comp _ _
    _ = yoneda.map α.right.unop.left ≫
        (AlgebraicSpace.compareSmallToBaseChange f k ≫ AlgebraicSpace.etaleBaseChangeSnd f W) :=
      congrArg _ (yonedaEquiv.symm_apply_apply _)
    _ = (yoneda.map α.right.unop.left ≫ AlgebraicSpace.compareSmallToBaseChange f k) ≫
        AlgebraicSpace.etaleBaseChangeSnd f W := (Category.assoc _ _ _).symm
    _ = AlgebraicSpace.compareSmallToBaseChange f k' ≫ AlgebraicSpace.etaleBaseChangeSnd f W :=
      congrArg (fun t => t ≫ AlgebraicSpace.etaleBaseChangeSnd f W) hα
    _ = yoneda.map (AlgebraicSpace.compareOverHom f k') :=
      (yonedaEquiv.symm_apply_apply _).symm

set_option backward.isDefEq.respectTransparency false in
/-- Functor from the small-étale Kan comma category to the CFG Kan comma category. -/
def restrictDirectImageComparison_indexMap {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (W : AlgebraicSpace.smallEtaleSite V) :
    restrictDirectImageComparison_smallIndex a eU eV W ⥤
      restrictDirectImageComparison_bigIndex a eV W where
  obj k := StructuredArrow.mk (restrictDirectImageComparison_indexArrow a eU eV W k)
  map {k k'} α :=
    StructuredArrow.homMk ((smallEtaleFunctor U Ucfg eU).map α.right.unop).op (by
      apply Quiver.Hom.unop_inj
      change (toCartesianBasedFunctor a).toFunctor.map
          ((smallEtaleFunctor U Ucfg eU).map α.right.unop) ≫
            restrictDirectImageComparison_indexHom a eU eV W k =
          restrictDirectImageComparison_indexHom a eU eV W k'
      dsimp only [restrictDirectImageComparison_indexHom]
      simp only [ObjectProperty.FullSubbicategory.toFunctor.compIso.hom.app,
        CategoryTheory.Functor.map_id, Category.id_comp]
      erw [NatTrans.naturality_assoc]
      congr 1
      have hn := (RepresentedDirectImage.targetCounitIso eV).inv.naturality
        ((toFunctor a).map ((smallEtaleFunctor U Ucfg eU).map α.right.unop))
      dsimp only [CategoryTheory.Functor.id_map, CategoryTheory.Functor.comp_map] at hn
      erw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp]
      congr 2
      let ψ := RepresentedDirectImage.presentedMorphism a eU eV
      let h := (smallEtaleToGroupoids U).map α.right.unop
      let x := (smallEtaleToGroupoids U).obj k.right.unop
      let x' := (smallEtaleToGroupoids U).obj k'.right.unop
      letI : V.toGroupoids.p.Faithful := by
        change ((CategoryOfElements.π V.functorOfPoints).leftOp).Faithful
        infer_instance
      apply V.toGroupoids.p.map_injective
      change V.toGroupoids.p.map ((toFunctor ψ).map h) ≫
          (((eqToIso (comm ψ)).app x).hom ≫
            AlgebraicSpace.compareOverHom (moduleComparisonSpaceMorphism a eU eV) k) =
        ((eqToIso (comm ψ)).app x').hom ≫
          AlgebraicSpace.compareOverHom (moduleComparisonSpaceMorphism a eU eV) k'
      calc
        _ = ((eqToIso (comm ψ)).app x').hom ≫ U.toGroupoids.p.map h ≫
            AlgebraicSpace.compareOverHom (moduleComparisonSpaceMorphism a eU eV) k :=
          (eqToIso (comm ψ)).hom.naturality_assoc h _
        _ = _ := congrArg (fun t => ((eqToIso (comm ψ)).app x').hom ≫ t)
          (restrictDirectImageComparison_compareOverHom_naturality
            (moduleComparisonSpaceMorphism a eU eV) W α))
  map_id _ := by
    apply StructuredArrow.hom_ext
    simp
  map_comp _ _ := by
    apply StructuredArrow.hom_ext
    simp

/-- The Kan diagrams agree after restriction along `restrictDirectImageComparison_indexMap`. -/
def restrictDirectImageComparison_diagIso {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite V) :
    restrictDirectImageComparison_indexMap a eU eV W ⋙
        restrictDirectImageComparison_bigDiag a eV H W ≅
      restrictDirectImageComparison_smallDiag a eU eV H W :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro k k' α
    simp
    rfl)

/-- Type-valued limits exist for the small-étale Kan diagram at `W ×_V U`. -/
instance restrictDirectImageComparison_smallDiag_hasLimit {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite V) :
    HasLimit (restrictDirectImageComparison_smallDiag a eU eV H W) :=
  AlgebraicSpace.EtaleTopos.allChartHasLimit U
    ((ToInternal.underlying (AlgebraicSpace.structureSheaf U)).obj ((restrictModules eU).obj H))
    ((AlgebraicSpace.etaleBaseChange (moduleComparisonSpaceMorphism a eU eV)).obj W)

/-- Type-valued limits exist after restriction along the index functor. -/
instance restrictDirectImageComparison_indexBigDiag_hasLimit {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite V) :
    HasLimit
      (restrictDirectImageComparison_indexMap a eU eV W ⋙
        restrictDirectImageComparison_bigDiag a eV H W) :=
  hasLimit_of_iso (restrictDirectImageComparison_diagIso a eU eV H W).symm

section RepresentedBigLimit

variable {Ucfg Vcfg : GroupoidsOver S} (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
variable (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
variable (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
variable (W : AlgebraicSpace.smallEtaleSite V)

include eU in
/-- The actual fibre-atlas/kernel-pair descent cone for the original CFG comma
diagram. Its construction uses each comma arrow into the specified target chart. -/
def restrictDirectImageComparison_bigCone :
    Cone (restrictDirectImageComparison_bigDiag a eV H W) :=
  RepresentedDirectImage.cone a eU eV
    ((ToInternal.underlying (etaleRingedSite Ucfg).structureSheaf).obj H)
    ((smallEtaleFunctor V Vcfg eV).obj W)

include eU in
/-- The universal lift evaluates the supplied cone at the actual fibre atlas
comma object and records its kernel-pair compatibility. -/
def restrictDirectImageComparison_bigConeIsLimit :
    IsLimit (restrictDirectImageComparison_bigCone a eU eV H W) :=
  RepresentedDirectImage.coneIsLimit a eU eV
    ((ToInternal.underlying (etaleRingedSite Ucfg).structureSheaf).obj H)
    ((smallEtaleFunctor V Vcfg eV).obj W)

include eU in
/-- The represented limit cone consists of the actual atlas descent carrier
and its concrete universal lift. -/
def restrictDirectImageComparison_bigLimitCone :
    LimitCone (restrictDirectImageComparison_bigDiag a eV H W) :=
  ⟨restrictDirectImageComparison_bigCone a eU eV H W,
    restrictDirectImageComparison_bigConeIsLimit a eU eV H W⟩

include eU in
/-- The given presentations provide a limit of the original comma diagram. -/
theorem restrictDirectImageComparison_bigDiag_hasLimit :
    HasLimit (restrictDirectImageComparison_bigDiag a eV H W) :=
  HasLimit.mk (restrictDirectImageComparison_bigLimitCone a eU eV H W)

end RepresentedBigLimit

/-- Restriction of compatible families from the CFG Kan comma category to the
small-étale Kan comma category. -/
def restrictDirectImageComparison_limitHom {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite V) :
    (restrictDirectImageComparison_bigLimitCone a eU eV H W).cone.pt ⟶
      limit (restrictDirectImageComparison_smallDiag a eU eV H W) :=
  limit.lift (restrictDirectImageComparison_smallDiag a eU eV H W)
    ((Cone.postcompose (restrictDirectImageComparison_diagIso a eU eV H W).hom).obj
      ((restrictDirectImageComparison_bigLimitCone a eU eV H W).cone.whisker
        (restrictDirectImageComparison_indexMap a eU eV W)))

/-- Evaluation of `a_small,*` of a restricted module at `W` compared with the
CFG pushforward at `u_V(W)`, via the two Kan-extension limits. -/
def restrictDirectImageComparison_rightEval {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite V) :
    -- Local instance justification (noncanonical choice): the supplied eU/eV presentations are not inferable from HasSmallCFGTypeSections a; install their proved certificate without adding a hypothesis.
    letI := hasSmallCFGTypeSections_ofRepresented a eU eV
    ((ToInternal.underlying (etaleRingedSite Ucfg).structureSheaf ⋙
          (etaleRingedToposHom a).toTopos.pushforward).obj H).obj.obj
        (op ((smallEtaleFunctor V Vcfg eV).obj W)) ⟶
      ((ToInternal.underlying (AlgebraicSpace.structureSheaf U) ⋙
            (AlgebraicSpace.ringedToposHom
                (moduleComparisonSpaceMorphism a eU eV)).toTopos.pushforward).obj
          ((restrictModules eU).obj H)).obj.obj (op W) :=
  -- Local instance justification (noncanonical choice): the supplied eU/eV presentations are not inferable from HasSmallCFGTypeSections a; install their proved certificate without adding a hypothesis.
  letI := hasSmallCFGTypeSections_ofRepresented a eU eV
  -- Local instance justification (proof-local temporary data): the diagram goal cannot infer the supplied eU/eV presentations; install their proved limit certificate for this use of the abstract limit API.
  letI := restrictDirectImageComparison_bigDiag_hasLimit a eU eV H W
  (restrictDirectImageComparison_bigConeIsLimit a eU eV H W).lift
      (limit.cone (restrictDirectImageComparison_bigDiag a eV H W)) ≫
    restrictDirectImageComparison_limitHom a eU eV H W ≫
      (limit.isoLimitCone
        ⟨AlgebraicSpace.EtaleTopos.allChartCone U
          ((ToInternal.underlying (AlgebraicSpace.structureSheaf U)).obj ((restrictModules eU).obj H))
          ((AlgebraicSpace.etaleBaseChange (moduleComparisonSpaceMorphism a eU eV)).obj W),
         AlgebraicSpace.EtaleTopos.allChartIsLimit U
          ((ToInternal.underlying (AlgebraicSpace.structureSheaf U)).obj ((restrictModules eU).obj H))
          ((AlgebraicSpace.etaleBaseChange (moduleComparisonSpaceMorphism a eU eV)).obj W)⟩).hom

/-- Sectionwise underlying comparison `(a_* H)|_{V_étale}(W) ⟶ a_small,* (H|_{U_étale})(W)`. -/
def restrictDirectImageComparisonUnderlying_app {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite V) :
    -- Local instance justification (noncanonical choice): the supplied eU/eV presentations are not inferable from HasSmallCFGTypeSections a; install their proved certificate without adding a hypothesis.
    letI := hasSmallCFGTypeSections_ofRepresented a eU eV
    ((ToInternal.underlying (AlgebraicSpace.structureSheaf V)).obj
        ((restrictModules eV).obj ((etaleModuleDirectImage a).obj H))).obj.obj (op W) ⟶
      ((ToInternal.underlying (AlgebraicSpace.structureSheaf V)).obj
        (((AlgebraicSpace.ringedToposHom
            (moduleComparisonSpaceMorphism a eU eV)).modulePushforward).obj
          ((restrictModules eU).obj H))).obj.obj (op W) :=
  -- Local instance justification (noncanonical choice): the supplied eU/eV presentations are not inferable from HasSmallCFGTypeSections a; install their proved certificate without adding a hypothesis.
  letI := hasSmallCFGTypeSections_ofRepresented a eU eV
  (restrictDirectImageComparison_leftEval a eV H W).hom ≫
    ((sheafToPresheaf Vcfg.etaleTopology (Type u)).map
        ((RingedSite.ToposHom.ModulePushforward.forgetIso
            (etaleRingedToposHom a)).hom.app H)).app
      (op ((smallEtaleFunctor V Vcfg eV).obj W)) ≫
      restrictDirectImageComparison_rightEval a eU eV H W ≫
        ((sheafToPresheaf (AlgebraicSpace.smallEtaleTopology V) (Type u)).map
            ((RingedSite.ToposHom.ModulePushforward.forgetIso
                (AlgebraicSpace.ringedToposHom
                  (moduleComparisonSpaceMorphism a eU eV))).inv.app
              ((restrictModules eU).obj H))).app (op W)

/-- Identification `restrict(h_* H) ⟶ h_small,* (restrict H)` of restricted
direct images, as an underlying type-valued sheaf morphism. -/
def restrictDirectImageComparisonUnderlying {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf) :
    -- Local instance justification (noncanonical choice): the supplied eU/eV presentations are not inferable from HasSmallCFGTypeSections a; install their proved certificate without adding a hypothesis.
    letI := hasSmallCFGTypeSections_ofRepresented a eU eV
    (ToInternal.underlying (AlgebraicSpace.structureSheaf V)).obj
        ((restrictModules eV).obj ((etaleModuleDirectImage a).obj H)) ⟶
      (ToInternal.underlying (AlgebraicSpace.structureSheaf V)).obj
        (((AlgebraicSpace.ringedToposHom
            (moduleComparisonSpaceMorphism a eU eV)).modulePushforward).obj
          ((restrictModules eU).obj H)) :=
  -- Local instance justification (noncanonical choice): the supplied eU/eV presentations are not inferable from HasSmallCFGTypeSections a; install their proved certificate without adding a hypothesis.
  letI := hasSmallCFGTypeSections_ofRepresented a eU eV
  CategoryTheory.ObjectProperty.homMk
    { app := fun W => restrictDirectImageComparisonUnderlying_app a eU eV H W.unop
      naturality := sorry }

/-- Restriction of CFG direct image compared with small étale pushforward of the
restriction. -/
def restrictDirectImageComparison {Ucfg Vcfg : GroupoidsOver S} (a : Ucfg ⟶ Vcfg)
    {U V : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (H : SheafOfModules.{u} (etaleRingedSite Ucfg).structureSheaf) :
    -- Local instance justification (noncanonical choice): the supplied eU/eV presentations are not inferable from HasSmallCFGTypeSections a; install their proved certificate without adding a hypothesis.
    letI := hasSmallCFGTypeSections_ofRepresented a eU eV
    (restrictModules eV).obj ((etaleModuleDirectImage a).obj H) ⟶
      ((AlgebraicSpace.ringedToposHom
          (moduleComparisonSpaceMorphism a eU eV)).modulePushforward).obj
        ((restrictModules eU).obj H) :=
  -- Local instance justification (noncanonical choice): the supplied eU/eV presentations are not inferable from HasSmallCFGTypeSections a; install their proved certificate without adding a hypothesis.
  letI := hasSmallCFGTypeSections_ofRepresented a eU eV
  homOfUnderlying (AlgebraicSpace.structureSheaf V)
    (restrictDirectImageComparisonUnderlying a eU eV H) sorry sorry

/-- Comparison `a_small^*(G |_{V_étale}) ⟶ (a^* G)|_{U_étale}` of restricted
module sheaves on `U_étale`, the mate of the restricted CFG unit. -/
def restrictPullbackComparison {Ucfg Vcfg : GroupoidsOver S} (a : Ucfg ⟶ Vcfg)
    {U V : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (G : SheafOfModules.{u} (etaleRingedSite Vcfg).structureSheaf) :
    (AlgebraicSpace.Modules.pullback (moduleComparisonSpaceMorphism a eU eV)).obj
        ((restrictModules eV).obj G) ⟶
      (restrictModules eU).obj ((etaleModuleInverseImage a).obj G) :=
  -- Local instance justification (noncanonical choice): the supplied eU/eV presentations are not inferable from HasSmallCFGTypeSections a; install their proved certificate without adding a hypothesis.
  letI := hasSmallCFGTypeSections_ofRepresented a eU eV
  ((AlgebraicSpace.Modules.pullbackPushforwardAdjunction
        (moduleComparisonSpaceMorphism a eU eV)).homEquiv
      ((restrictModules eV).obj G)
      ((restrictModules eU).obj ((etaleModuleInverseImage a).obj G))).symm
    ((restrictModules eV).map
        (etaleModuleUnit a G) ≫
      restrictDirectImageComparison a eU eV ((etaleModuleInverseImage a).obj G))

/-- The push-form comparison
`g^* F |_{V_étale} ⟶ a_small,* (f^* F |_{U_étale})` of `𝒪_{V_étale}`-modules:
the restricted unit of `a^* ⊣ a_*`, transported along `φ` and followed by
the direct-image comparison. -/
def moduleComparisonSpacePushforward {X Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) (f : Ucfg ⟶ X) (g : Vcfg ⟶ X) (φ : a ≫ g ≅ f)
    {U V : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (F : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    (restrictModules eV).obj ((etaleModuleInverseImage g).obj F) ⟶
      ((AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism a eU eV)).modulePushforward).obj
        ((restrictModules eU).obj ((etaleModuleInverseImage f).obj F)) :=
  -- Local instance justification (noncanonical choice): the supplied eU/eV presentations are not inferable from HasSmallCFGTypeSections a; install their proved certificate without adding a hypothesis.
  letI := hasSmallCFGTypeSections_ofRepresented a eU eV
  (restrictModules eV).map
      (etaleModuleUnit a ((etaleModuleInverseImage g).obj F) ≫
        (etaleModuleDirectImage a).map
          ((etaleModuleInverseImage_twoCell a f g φ).hom.app F)) ≫
    restrictDirectImageComparison a eU eV ((etaleModuleInverseImage f).obj F)

/-- The comparison morphism
`c_φ : a_small^*(g^* F |_{V_étale}) ⟶ f^* F |_{U_étale}` of
`𝒪_{U_étale}`-modules, obtained as the adjunct of
`moduleComparisonSpacePushforward`. -/
def moduleComparisonSpace {X Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) (f : Ucfg ⟶ X) (g : Vcfg ⟶ X) (φ : a ≫ g ≅ f)
    {U V : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (F : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    (AlgebraicSpace.Modules.pullback (moduleComparisonSpaceMorphism a eU eV)).obj
        ((restrictModules eV).obj ((etaleModuleInverseImage g).obj F)) ⟶
      (restrictModules eU).obj ((etaleModuleInverseImage f).obj F) :=
  -- Local instance justification (noncanonical choice): the supplied eU/eV presentations are not inferable from HasSmallCFGTypeSections a; install their proved certificate without adding a hypothesis.
  letI := hasSmallCFGTypeSections_ofRepresented a eU eV
  ((AlgebraicSpace.Modules.pullbackPushforwardAdjunction
        (moduleComparisonSpaceMorphism a eU eV)).homEquiv
      ((restrictModules eV).obj ((etaleModuleInverseImage g).obj F))
      ((restrictModules eU).obj ((etaleModuleInverseImage f).obj F))).symm
    (moduleComparisonSpacePushforward a f g φ eU eV F)

/-- `moduleComparisonSpace` is the adjunct of `moduleComparisonSpacePushforward`
along the small-étale module adjunction of `a`. -/
theorem moduleComparisonSpace_adjunct {X Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) (f : Ucfg ⟶ X) (g : Vcfg ⟶ X) (φ : a ≫ g ≅ f)
    {U V : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (F : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    (AlgebraicSpace.Modules.pullbackPushforwardAdjunction
        (moduleComparisonSpaceMorphism a eU eV)).homEquiv
        ((restrictModules eV).obj ((etaleModuleInverseImage g).obj F))
        ((restrictModules eU).obj ((etaleModuleInverseImage f).obj F))
        (moduleComparisonSpace a f g φ eU eV F) =
      moduleComparisonSpacePushforward a f g φ eU eV F := by
  exact Equiv.apply_symm_apply _ _

/-- The push-form of the comparison is the restricted
unit of `a^* ⊣ a_*`, transported along `φ` and followed by the direct-image comparison. -/
theorem moduleComparisonSpace_spec {X Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) (f : Ucfg ⟶ X) (g : Vcfg ⟶ X) (φ : a ≫ g ≅ f)
    {U V : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (F : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    -- Local instance justification (noncanonical choice): the supplied eU/eV presentations are not inferable from HasSmallCFGTypeSections a; install their proved certificate without adding a hypothesis.
    letI := hasSmallCFGTypeSections_ofRepresented a eU eV
    moduleComparisonSpacePushforward a f g φ eU eV F =
      (restrictModules eV).map
          (etaleModuleUnit a ((etaleModuleInverseImage g).obj F) ≫
            (etaleModuleDirectImage a).map
              ((etaleModuleInverseImage_twoCell a f g φ).hom.app F)) ≫
        restrictDirectImageComparison a eU eV
          ((etaleModuleInverseImage f).obj F) :=
  rfl

end AlgebraicGeometry.GroupoidsOver
