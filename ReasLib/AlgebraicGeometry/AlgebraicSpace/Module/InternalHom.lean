module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Sheafification.OverAbelian
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.LocalSectionMul

/-! # Internal Hom of module sheaves on algebraic spaces -/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.InternalHom

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Local module morphisms on the small atlas basis of a slice. -/
abbrev Section (F G : Modules X) (U : smallEtaleSite X) : Type u :=
  (PresheafOfModules.pushforward₀
      (CostructuredArrow.toOver
        (PullbackFactory.SmallAtlas.inclusion (AtlasInput.scheme X) (AtlasInput.map X)) U)
      ((commRingSheaf X).over U).obj).obj (((toCommModules X).obj F).over U).val ⟶
    (PresheafOfModules.pushforward₀
      (CostructuredArrow.toOver
        (PullbackFactory.SmallAtlas.inclusion (AtlasInput.scheme X) (AtlasInput.map X)) U)
      ((commRingSheaf X).over U).obj).obj (((toCommModules X).obj G).over U).val

set_option maxHeartbeats 800000 in
/-- Restriction and dense-subsite extension identify local morphisms with their small codes. -/
def sectionEquiv (F G : Modules X) (U : smallEtaleSite X) :
    Section F G U ≃ (F.over U ⟶ G.over U) := by
  let j := CostructuredArrow.toOver
    (PullbackFactory.SmallAtlas.inclusion (AtlasInput.scheme X) (AtlasInput.map X)) U
  let res (M : Modules X) :=
    (PresheafOfModules.pushforward₀ j ((commRingSheaf X).over U).obj).obj
      (((toCommModules X).obj M).over U).val
  refine
    { toFun := fun s =>
        { val :=
            { app := fun V => ModuleCat.ofHom
                (X := (F.over U).val.obj V) (Y := (G.over U).val.obj V)
                { toFun := fun x =>
                    (@Functor.IsCoverDense.sheafHom _ _ _ _
                      ((smallEtaleTopology X).over U) AddCommGrpCat.{u} inferInstance
                      j
                      (PullbackFactory.SmallAtlas.over_coverDense
                        (AtlasInput.scheme X) (AtlasInput.map X)
                        (AtlasInput.locallySurjective X) U)
                      inferInstance (((toCommModules X).obj F).over U).val.presheaf
                      ((SheafOfModules.toSheaf _).obj (((toCommModules X).obj G).over U))
                      ((PresheafOfModules.toPresheaf _).map s)).app V x
                  map_add' := ?_
                  map_smul' := ?_ }
              naturality := ?_ } }
      invFun := fun s =>
        { app := fun V => ModuleCat.ofHom
            (X := (res F).obj V) (Y := (res G).obj V)
            { toFun := fun x => s.val.app (j.op.obj V) x
              map_add' := ?_
              map_smul' := ?_ }
          naturality := ?_ }
      left_inv := ?_
      right_inv := ?_ }
  all_goals sorry

/-- Local sections of the target act on local morphisms by postcomposition. -/
def sectionModule (F G : Modules X) (U : smallEtaleSite X) :
    ModuleCat.{u} ((commStructureSheaf X).obj.obj (op U)) := by
  let j := CostructuredArrow.toOver
    (PullbackFactory.SmallAtlas.inclusion (AtlasInput.scheme X) (AtlasInput.map X)) U
  let res (M : Modules X) :=
    (PresheafOfModules.pushforward₀ j ((commRingSheaf X).over U).obj).obj
      (((toCommModules X).obj M).over U).val
  let action : (commStructureSheaf X).obj.obj (op U) →+* End (res G) :=
    { toFun := fun r =>
        (PresheafOfModules.pushforward₀ j ((commRingSheaf X).over U).obj).map
          (SheafOfModules.sectionAction (commStructureSheaf X)
            ((toCommModules X).obj G) U r).val
      map_zero' := by
        rw [map_zero]
        apply PresheafOfModules.hom_ext
        intro V
        rfl
      map_one' := by
        rw [map_one]
        apply PresheafOfModules.hom_ext
        intro V
        rfl
      map_add' r s := by
        rw [map_add]
        apply PresheafOfModules.hom_ext
        intro V
        rfl
      map_mul' r s := by
        rw [map_mul]
        apply PresheafOfModules.hom_ext
        intro V
        rfl }
  exact @ModuleCat.of _ _ (Section F G U) inferInstance
    (Module.compHom _ action)

/-- Restriction of local morphisms along an arrow of étale charts. -/
def restrict (F G : Modules X) {U V : smallEtaleSite X} (i : V ⟶ U) :
    sectionModule F G U ⟶
      (ModuleCat.restrictScalars ((commStructureSheaf X).obj.map i.op).hom).obj
        (sectionModule F G V) := by
  refine ModuleCat.ofHom
    (X := sectionModule F G U)
    (Y := (ModuleCat.restrictScalars ((commStructureSheaf X).obj.map i.op).hom).obj
      (sectionModule F G V))
    { toFun := fun s => (sectionEquiv F G V).symm
        (((SheafOfModules.overFunctorMap (structureSheaf X) i).inv.app F) ≫
          (SheafOfModules.overMap (structureSheaf X) i).map (sectionEquiv F G U s) ≫
          ((SheafOfModules.overFunctorMap (structureSheaf X) i).hom.app G))
      map_add' := ?_
      map_smul' := ?_ }
  all_goals sorry

/-- The presheaf of local module morphisms, with restriction of scalars along chart arrows. -/
def presheaf (F G : Modules X) : PresheafOfModules.{u} (commRingSheaf X).obj := by
  refine
    { obj := fun U => sectionModule F G U.unop
      map := fun i => restrict F G i.unop
      map_id := ?_
      map_comp := ?_ }
  all_goals sorry

/-- The sheaf of local morphisms between two structure-sheaf modules. -/
def obj (F G : Modules X) : Modules X :=
  (ofCommModules X).obj { val := presheaf F G, isSheaf := by sorry }

/-- Sections of internal Hom identify with module morphisms on the corresponding slice. -/
def sectionsEquiv (F G : Modules X) (U : smallEtaleSite X) :
    (obj F G).val.obj (op U) ≃ (F.over U ⟶ G.over U) :=
  sectionEquiv F G U

/-- Precomposition of local module morphisms by a fixed module morphism. -/
def pre {F F' : Modules X} (f : F ⟶ F') (G : Modules X) :
    obj F' G ⟶ obj F G := by
  let basisMap (U : smallEtaleSite X) :=
    (PresheafOfModules.pushforward₀
      (CostructuredArrow.toOver
        (PullbackFactory.SmallAtlas.inclusion (AtlasInput.scheme X) (AtlasInput.map X)) U)
      ((commRingSheaf X).over U).obj).map (((toCommModules X).map f).over U).val
  refine (ofCommModules X).map
    { val :=
        { app := fun U => ModuleCat.ofHom
            (X := sectionModule F' G U.unop) (Y := sectionModule F G U.unop)
            { toFun := fun s => basisMap U.unop ≫ s
              map_add' := ?_
              map_smul' := ?_ }
          naturality := ?_ } }
  all_goals sorry

/-- Postcomposition of local module morphisms by a fixed module morphism. -/
def post (F : Modules X) {G G' : Modules X} (g : G ⟶ G') :
    obj F G ⟶ obj F G' := by
  let basisMap (U : smallEtaleSite X) :=
    (PresheafOfModules.pushforward₀
      (CostructuredArrow.toOver
        (PullbackFactory.SmallAtlas.inclusion (AtlasInput.scheme X) (AtlasInput.map X)) U)
      ((commRingSheaf X).over U).obj).map (((toCommModules X).map g).over U).val
  refine (ofCommModules X).map
    { val :=
        { app := fun U => ModuleCat.ofHom
            (X := sectionModule F G U.unop) (Y := sectionModule F G' U.unop)
            { toFun := fun s => s ≫ basisMap U.unop
              map_add' := ?_
              map_smul' := ?_ }
          naturality := ?_ } }
  all_goals sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.InternalHom
