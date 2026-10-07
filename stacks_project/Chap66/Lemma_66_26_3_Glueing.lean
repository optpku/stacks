module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Whiskering
public import stacks_project.Chap66.Lemma_66_18_13_Glueing
public import stacks_project.Chap66.Lemma_66_26_1_Pullback

/-!
# Glueing modules on small étale sites of algebraic spaces

A sheaf of `𝒪_X`-modules on `X_étale` determines an `𝒪_U`-module on `U_étale` for every
object `U` of `X_étale`, together with module-pullback transition isomorphisms along
morphisms of `X_étale`. This module packages those compatible systems.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.SmallEtaleGlueing
  (etale_siteHom idObj idObjHom ofOverMap_id ofOverMap_comp ofOverMap_triangle)
open CategoryTheory.Sheaf.InternalModule

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtaleModuleGlueing

variable {S : Scheme.{u}}

/-- The structure morphism of an object of `X_étale` is étale. -/
instance etale_objHom {X : AlgebraicSpace S} (U : smallEtaleSite X) : Etale U.hom :=
  U.prop

/-- Pullback of `𝒪`-modules along a morphism of `X_étale`, as module pullback of
`f_small`. -/
noncomputable def pullback {X : AlgebraicSpace S} {U V : smallEtaleSite X} (f : V ⟶ U) :
    (ofOver U.left).Modules ⥤ (ofOver V.left).Modules :=
  Modules.pullback (ofOverMap f.left)

/-- Pullback of modules along a morphism of `X_étale` is module pullback of the induced
étale map of algebraic spaces. -/
theorem pullback_eq {X : AlgebraicSpace S} {U V : smallEtaleSite X} (f : V ⟶ U) :
    pullback f = Modules.pullback (ofOverMap f.left) :=
  rfl

/-- The identification `𝒢|_{X_étale} ≅ f^* 𝒢` along a morphism of `X_étale`. -/
noncomputable def pullbackIsoRestrict {X : AlgebraicSpace S} {U V : smallEtaleSite X}
    (f : V ⟶ U) :
    pullback f ≅ Modules.restrictFunctor (ofOverMap f.left) :=
  (Modules.restrictFunctorIsoPullback (ofOverMap f.left)).symm

/-- Restriction of modules along an identity morphism is canonically the identity. -/
noncomputable def restrictFunctorId (Y : AlgebraicSpace S) :
    Modules.restrictFunctor (𝟙 Y) ≅ 𝟭 Y.Modules :=
  NatIso.ofComponents
    (fun M ↦
      { hom :=
          homOfUnderlying (structureSheaf Y)
            (InducedCategory.homMk
              { app := fun _ ↦ 𝟙 _
                naturality := fun _ _ _ ↦ sorry })
            sorry sorry
        inv :=
          homOfUnderlying (structureSheaf Y)
            (InducedCategory.homMk
              { app := fun _ ↦ 𝟙 _
                naturality := fun _ _ _ ↦ sorry })
            sorry sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Pullback of modules along an identity morphism is canonically the identity. -/
noncomputable def modulesPullbackId (Y : AlgebraicSpace S) :
    Modules.pullback (𝟙 Y) ≅ 𝟭 Y.Modules :=
  (Modules.restrictFunctorIsoPullback (𝟙 Y)).symm ≪≫ restrictFunctorId Y

/-- Pullback along an identity is canonically isomorphic to the identity on small étale
modules. -/
noncomputable def pullbackId {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    pullback (𝟙 U) ≅ 𝟭 (ofOver U.left).Modules :=
  eqToIso (congrArg (fun h ↦ Modules.pullback h) (ofOverMap_id U.left)) ≪≫
    modulesPullbackId (ofOver U.left)

/-- Restriction of modules along an étale composite is the composite of the restrictions. -/
noncomputable def restrictFunctorComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    (g : Y ⟶ Z) [Etale g] :
    Modules.restrictFunctor g ⋙ Modules.restrictFunctor f ≅ Modules.restrictFunctor (f ≫ g) :=
  NatIso.ofComponents
    (fun M ↦
      { hom :=
          homOfUnderlying (structureSheaf X)
            (InducedCategory.homMk
              { app := fun _ ↦ 𝟙 _
                naturality := fun _ _ _ ↦ sorry })
            sorry sorry
        inv :=
          homOfUnderlying (structureSheaf X)
            (InducedCategory.homMk
              { app := fun _ ↦ 𝟙 _
                naturality := fun _ _ _ ↦ sorry })
            sorry sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Successive pullbacks of modules along étale morphisms identify with pullback along the
composite. -/
noncomputable def modulesPullbackComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    (g : Y ⟶ Z) [Etale g] :
    Modules.pullback g ⋙ Modules.pullback f ≅ Modules.pullback (f ≫ g) :=
  Functor.isoWhiskerRight (Modules.restrictFunctorIsoPullback g).symm (Modules.pullback f) ≪≫
    Functor.isoWhiskerLeft (Modules.restrictFunctor g)
      (Modules.restrictFunctorIsoPullback f).symm ≪≫
    restrictFunctorComp f g ≪≫ Modules.restrictFunctorIsoPullback (f ≫ g)

/-- Successive pullbacks of small étale modules are canonically isomorphic to pullback along
the composite. -/
noncomputable def pullbackComp {X : AlgebraicSpace S} {U V W : smallEtaleSite X}
    (f : V ⟶ U) (g : W ⟶ V) :
    pullback f ⋙ pullback g ≅ pullback (g ≫ f) :=
  modulesPullbackComp (ofOverMap g.left) (ofOverMap f.left) ≪≫
    eqToIso (congrArg (fun h ↦ Modules.pullback h) (ofOverMap_comp f.left g.left).symm)

/-- A compatible system of modules on the small étale sites of schemes étale over an
algebraic space. -/
structure Object {S : Scheme.{u}} (X : AlgebraicSpace S) where
  /-- The sheaf of `𝒪_U`-modules on the small étale site of a scheme étale over `X`. -/
  obj (U : smallEtaleSite X) : (ofOver U.left).Modules
  /-- The module-pullback transition isomorphism `c_f : f_small^* F_U ≅ F_{U'}`. -/
  transition {U V : smallEtaleSite X} (f : V ⟶ U) : (pullback f).obj (obj U) ≅ obj V
  /-- The transition along an identity is the canonical identity comparison. -/
  transition_id (U : smallEtaleSite X) :
    transition (𝟙 U) = (pullbackId U).app (obj U)
  /-- The transitions satisfy the module-pullback cocycle
  `c_g ∘ g_small^* c_f = c_{f ∘ g}`. -/
  transition_comp {U V W : smallEtaleSite X} (f : V ⟶ U) (g : W ⟶ V) :
    (pullbackComp f g).app (obj U) ≪≫ transition (g ≫ f) =
      (pullback g).mapIso (transition f) ≪≫ transition g

namespace Object

variable {X : AlgebraicSpace S}

/-- The fields of a compatible small-étale module system express identity and the cocycle
condition for its transition isomorphisms. -/
theorem spec (F : Object X) :
    (∀ U : smallEtaleSite X, F.transition (𝟙 U) = (pullbackId U).app (F.obj U)) ∧
      (∀ {U V W : smallEtaleSite X} (f : V ⟶ U) (g : W ⟶ V),
        (pullbackComp f g).app (F.obj U) ≪≫ F.transition (g ≫ f) =
          (pullback g).mapIso (F.transition f) ≪≫ F.transition g) :=
  sorry

end Object

/-- A morphism of compatible small-étale module systems is a componentwise module morphism
commuting with every transition isomorphism. -/
@[ext]
structure Hom {X : AlgebraicSpace S} (F G : Object X) where
  /-- The component over an object of `X_étale`. -/
  app (U : smallEtaleSite X) : F.obj U ⟶ G.obj U
  /-- Component maps commute with module-pullback transitions. -/
  naturality {U V : smallEtaleSite X} (f : V ⟶ U) :
    CommSq ((pullback f).map (app U)) (F.transition f).hom (G.transition f).hom (app V)

namespace Hom

variable {X : AlgebraicSpace S}

/-- The identity compatible morphism. -/
def id (F : Object X) : Hom F F where
  app U := 𝟙 (F.obj U)
  naturality _ := sorry

/-- Composition of compatible morphisms. -/
def comp {F G H : Object X} (α : Hom F G) (β : Hom G H) : Hom F H where
  app U := α.app U ≫ β.app U
  naturality _ := sorry

end Hom

/-- The category of compatible module systems, bundled without installing a global category
instance on the explicit object structure. -/
noncomputable def category (X : AlgebraicSpace S) : Cat :=
  { α := Object X
    str :=
      { Hom := Hom
        id := Hom.id
        comp := Hom.comp
        id_comp := sorry
        comp_id := sorry
        assoc := sorry } }

/-- Restriction of modules along the structure morphism of an object of `X_étale`. -/
noncomputable def restrictFunctor_hom {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    X.Modules ⥤ (ofOver U.left).Modules :=
  @Modules.restrictFunctor _ _ _ U.hom U.prop

/-- Identification of restriction along a structure morphism with module pullback. -/
noncomputable def restrictFunctorIsoPullback_hom {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    restrictFunctor_hom U ≅ Modules.pullback U.hom :=
  @Modules.restrictFunctorIsoPullback _ _ _ U.hom U.prop

/-- The sheaf of modules on `U_étale` obtained by module pullback along the structure morphism
of `U`. -/
noncomputable def fromModulesObj {X : AlgebraicSpace S} (F : X.Modules) (U : smallEtaleSite X) :
    (ofOver U.left).Modules :=
  (Modules.pullback U.hom).obj F

/-- Restriction along a morphism of `X_étale` then along a structure morphism identifies with
restriction along the triangle composite. -/
noncomputable def restrictFunctorComp_hom {X : AlgebraicSpace S} {U V : smallEtaleSite X}
    (f : V ⟶ U) :
    restrictFunctor_hom U ⋙ Modules.restrictFunctor (ofOverMap f.left) ≅
      @Modules.restrictFunctor _ _ _ (ofOverMap f.left ≫ U.hom)
        (@Etale.etale_comp _ _ _ (ofOverMap f.left) _ U.hom (etale_siteHom f) U.prop) :=
  NatIso.ofComponents
    (fun M ↦
      { hom :=
          homOfUnderlying (structureSheaf (ofOver V.left))
            (InducedCategory.homMk
              { app := fun _ ↦ 𝟙 _
                naturality := fun _ _ _ ↦ sorry })
            sorry sorry
        inv :=
          homOfUnderlying (structureSheaf (ofOver V.left))
            (InducedCategory.homMk
              { app := fun _ ↦ 𝟙 _
                naturality := fun _ _ _ ↦ sorry })
            sorry sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Successive pullbacks along a morphism of `X_étale` and a structure morphism identify with
pullback along the triangle composite. -/
noncomputable def modulesPullbackComp_hom {X : AlgebraicSpace S} {U V : smallEtaleSite X}
    (f : V ⟶ U) :
    Modules.pullback U.hom ⋙ Modules.pullback (ofOverMap f.left) ≅
      Modules.pullback (ofOverMap f.left ≫ U.hom) :=
  Functor.isoWhiskerRight (restrictFunctorIsoPullback_hom U).symm
      (Modules.pullback (ofOverMap f.left)) ≪≫
    Functor.isoWhiskerLeft (restrictFunctor_hom U)
      (Modules.restrictFunctorIsoPullback (ofOverMap f.left)).symm ≪≫
    restrictFunctorComp_hom f ≪≫
      @Modules.restrictFunctorIsoPullback _ _ _ (ofOverMap f.left ≫ U.hom)
        (@Etale.etale_comp _ _ _ (ofOverMap f.left) _ U.hom (etale_siteHom f) U.prop)

/-- The canonical transition of the compatible system associated to a sheaf of modules on
`X_étale`. -/
noncomputable def fromModulesTransition {X : AlgebraicSpace S} (F : X.Modules)
    {U V : smallEtaleSite X} (f : V ⟶ U) :
    (pullback f).obj (fromModulesObj F U) ≅ fromModulesObj F V :=
  (modulesPullbackComp_hom f).app F ≪≫
    eqToIso (congrArg (fun h ↦ (Modules.pullback h).obj F) (ofOverMap_triangle f))

namespace Object

variable {X : AlgebraicSpace S}

/-- The compatible system of small étale modules obtained by module pullback from a sheaf of
modules on `X_étale`. -/
noncomputable def ofModules (F : X.Modules) : Object X where
  obj := fromModulesObj F
  transition := fromModulesTransition F
  transition_id _ := sorry
  transition_comp _ _ := sorry

end Object

/-- A morphism of modules on `X_étale` induces the componentwise compatible morphism
between their pullback systems. -/
noncomputable def fromModulesMap {X : AlgebraicSpace S} {F G : X.Modules} (η : F ⟶ G) :
    Hom (Object.ofModules F) (Object.ofModules G) where
  app U := (Modules.pullback U.hom).map η
  naturality _ := sorry

/-- Module pullback of sheaves of modules on `X_étale` to compatible systems on all
`U_étale`. -/
noncomputable def fromModules (X : AlgebraicSpace S) :
    X.Modules ⥤ category X where
  obj := Object.ofModules
  map := fromModulesMap
  map_id := sorry
  map_comp := sorry

variable {X : AlgebraicSpace S}

/-- The object of the compatible system associated to a sheaf of modules is pullback along
the structure morphism. -/
theorem fromModules_obj (F : X.Modules) (U : smallEtaleSite X) :
    ((fromModules X).obj F).obj U = (Modules.pullback U.hom).obj F :=
  rfl

/-- The transition of the compatible system associated to a sheaf of modules is the
functoriality isomorphism of module pullback. -/
theorem fromModules_transition (F : X.Modules) {U V : smallEtaleSite X} (f : V ⟶ U) :
    ((fromModules X).obj F).transition f = fromModulesTransition F f :=
  rfl

/-- Sections of a compatible system at an object of `X_étale`, as the module of `F_U` at the
identity object of `U_étale`. -/
noncomputable def toModulesObj (G : Object X) (U : smallEtaleSite X) :
    ModuleCat ((structureSheaf X).obj.obj (op U)) :=
  (G.obj U).val.obj (op (idObj U.left))

/-- The underlying function of reconstructed restriction along a morphism of `X_étale`. -/
noncomputable def toModulesMapType (G : Object X) {U V : smallEtaleSite X} (f : V ⟶ U) :
    ((G.obj U).val.obj (op (idObj U.left)) : Type u) ⟶
      ((G.obj V).val.obj (op (idObj V.left)) : Type u) :=
  ToInternal.restrictionApp (structureSheaf (ofOver U.left)) (G.obj U) (idObjHom f).op ≫
    ((Modules.pullbackIsoInverseImage (ofOverMap f.left)).inv.app (G.obj U)).hom.app
      (op (idObj V.left)) ≫
    ToInternal.carrierMapApp (structureSheaf (ofOver V.left)) (G.transition f).hom
      (op (idObj V.left))

/-- Linearity of reconstructed restriction along a morphism of `X_étale`. -/
noncomputable def toModulesMapLinear (G : Object X) {U V : smallEtaleSite X} (f : V ⟶ U) :
    (toModulesObj G U : Type u) →ₗ[(structureSheaf X).obj.obj (op U)]
      ((ModuleCat.restrictScalars ((structureSheaf X).obj.map f.op).hom).obj
        (toModulesObj G V) : Type u) where
  toFun := toModulesMapType G f
  map_add' := sorry
  map_smul' := sorry

/-- Restriction of reconstructed modules along a morphism of `X_étale`. -/
noncomputable def toModulesMap (G : Object X) {U V : smallEtaleSite X} (f : V ⟶ U) :
    toModulesObj G U ⟶
      (ModuleCat.restrictScalars ((structureSheaf X).obj.map f.op).hom).obj (toModulesObj G V) :=
  ConcreteCategory.ofHom (toModulesMapLinear G f)

/-- The presheaf of modules on `X_étale` reconstructed from identity-object sections of a
compatible system. -/
noncomputable def toModulesPresheaf (G : Object X) :
    PresheafOfModules (structureSheaf X).obj where
  obj U := toModulesObj G U.unop
  map f := toModulesMap G f.unop
  map_id := sorry
  map_comp := sorry

/-- The reconstructed presheaf of a compatible module system is a sheaf on `X_étale`. -/
theorem toModules_isSheaf (G : Object X) :
    Presheaf.IsSheaf (smallEtaleTopology X) (toModulesPresheaf G).presheaf :=
  sorry

/-- Reconstruction of a sheaf of modules on `X_étale` from a compatible system of modules on
all `U_étale`. -/
noncomputable def toModules (X : AlgebraicSpace S) :
    category X ⥤ X.Modules where
  obj G := ⟨toModulesPresheaf G, toModules_isSheaf G⟩
  map {G H} α :=
    { val :=
        { app := fun U ↦ (α.app U.unop).val.app (op (idObj U.unop.left))
          naturality := sorry } }
  map_id := sorry
  map_comp := sorry

/-- Reconstructed sections of a compatible module system at `U` are the sections of `F_U` at
the identity object of `U_étale`. -/
theorem toModules_obj (G : Object X) (U : smallEtaleSite X) :
    (((toModules X).obj G).val.obj (op U)) = (G.obj U).val.obj (op (idObj U.left)) :=
  rfl

/-- Module pullback from sheaves of modules on `X_étale` to compatible systems on all small
étale sites is an equivalence of categories. -/
instance fromModules_isEquivalence (X : AlgebraicSpace S) :
    (fromModules X).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.SmallEtaleModuleGlueing
