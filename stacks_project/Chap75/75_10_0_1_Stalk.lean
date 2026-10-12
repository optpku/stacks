/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Elements
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Stalk
public import stacks_project.Chap66.«66_26_1_1_Restrict»
public import stacks_project.Chap66.Lemma_66_29_4_Stalk

/-!
# Stalks of étale restriction of modules on algebraic spaces

For an étale morphism `j : U ⟶ X` of algebraic spaces, the stalk of `restrict F j` at a
geometric point `ubar` of `U` is canonically isomorphic to the stalk of `F` at `ubar.map j`,
after transporting scalars along the identity-on-sections map of étale local rings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open AlgebraicGeometry.AlgebraicSpace.Modules ModuleCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

variable {S : Scheme.{u}} {U X : AlgebraicSpace S}

/-- The lift of `ubar.map j` through `restrictPostcompose j` of an étale neighbourhood of
`ubar`, obtained by retaining the underlying morphism over `S`. -/
def restrictPostcomposeLift (j : U ⟶ X) [Etale j] (ubar : GeometricPoint U)
    {V : smallEtaleSite U} (l : OverLift ubar V) :
    OverLift (ubar.map j) ((restrictPostcompose j).obj V) :=
  OverLift.of l.hom sorry

/-- Postcomposition of étale neighbourhoods of `ubar` along `j`, sending a neighbourhood of
`ubar` to the same underlying scheme viewed as a neighbourhood of `ubar.map j`. -/
def restrictNeighborhood (j : U ⟶ X) [Etale j] (ubar : GeometricPoint U) :
    (toSmallEtalePoint ubar).fiber.Elements ⥤
      (toSmallEtalePoint (ubar.map j)).fiber.Elements where
  obj N := ⟨(restrictPostcompose j).obj N.1, restrictPostcomposeLift j ubar N.2⟩
  map f := ⟨(restrictPostcompose j).map f.val, sorry⟩
  map_id := sorry
  map_comp := sorry

/-- Postcomposition of neighbourhoods is initial: étale neighbourhoods of `ubar` are cofinal
among étale neighbourhoods of `ubar.map j`. -/
instance restrictNeighborhood_initial (j : U ⟶ X) [Etale j] (ubar : GeometricPoint U) :
    (restrictNeighborhood j ubar).Initial :=
  sorry

/-- Forgetting the lift, `restrictNeighborhood` is postcomposition of the underlying étale
objects. -/
def restrictNeighborhood_πIso (j : U ⟶ X) [Etale j] (ubar : GeometricPoint U) :
    CategoryOfElements.π (toSmallEtalePoint ubar).fiber ⋙ restrictPostcompose j ≅
      restrictNeighborhood j ubar ⋙
        CategoryOfElements.π (toSmallEtalePoint (ubar.map j)).fiber :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {U X : AlgebraicSpace S}

/-- The functor-of-points lift of `ubar` through the fibre product `U ×_X W`. -/
def restrictNeighborhoodRefineSpaceLift (j : U ⟶ X) [Etale j] (ubar : GeometricPoint U)
    {W : smallEtaleSite X} (l : OverLift (ubar.map j) W) :
    ofOver ubar.overObj ⟶ etaleBaseChangeSpace j W :=
  pullback.lift (f := homFunctor j) (g := homFunctor W.hom)
    ubar.hom (ofOverMap l.hom) sorry

/-- The structure morphism of the packaged fibre-product neighbourhood is étale. -/
instance etale_restrictNeighborhoodRefineObj (j : U ⟶ X) [Etale j] (ubar : GeometricPoint U)
    {W : smallEtaleSite X} (l : OverLift (ubar.map j) W) :
    Etale (restrictNeighborhoodRefineSpaceLift j ubar l ≫ etaleBaseChangeHom j W) :=
  sorry

/-- The fibre-product neighbourhood of `ubar` obtained by packaging the étale projection
`etaleBaseChangeHom j W` after the lift of `ubar`, via `smallEtaleSite.mk`. -/
def restrictNeighborhoodRefineObj (j : U ⟶ X) [Etale j] (ubar : GeometricPoint U)
    {W : smallEtaleSite X} (l : OverLift (ubar.map j) W) : smallEtaleSite U :=
  smallEtaleSite.mk
    (restrictNeighborhoodRefineSpaceLift j ubar l ≫ etaleBaseChangeHom j W)

/-- The lift of `ubar` through the packaged fibre-product neighbourhood. -/
def restrictNeighborhoodRefineLift (j : U ⟶ X) [Etale j] (ubar : GeometricPoint U)
    {W : smallEtaleSite X} (l : OverLift (ubar.map j) W) :
    OverLift ubar (restrictNeighborhoodRefineObj j ubar l) :=
  OverLift.of (𝟙 ubar.overObj) sorry

/-- The projection `U ×_X W ⟶ W` in the small étale site of `X`, as `etaleBaseChangeSnd`
after the lift of `ubar`. -/
def restrictNeighborhoodRefineHom (j : U ⟶ X) [Etale j] (ubar : GeometricPoint U)
    {W : smallEtaleSite X} (l : OverLift (ubar.map j) W) :
    (restrictPostcompose j).obj (restrictNeighborhoodRefineObj j ubar l) ⟶ W :=
  MorphismProperty.CostructuredArrow.homMk
    (toOverHom
      (restrictNeighborhoodRefineSpaceLift j ubar l ≫ etaleBaseChangeSnd j W))
    trivial sorry

/-- Identity-on-sections comparison of structure sheaves after postcomposition of étale
objects. -/
def restrictStructurePresheafIso (j : U ⟶ X) [Etale j] :
    (structureSheaf U).obj ≅ (restrictPostcompose j).op ⋙ (structureSheaf X).obj :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry

/-- Identity-on-sections map of étale local rings `𝒪_{U, ubar} →+* 𝒪_{X, ubar.map j}`,
sending the germ of a section over `V` to the germ of the same section over the
postcomposed neighbourhood of `ubar.map j`. -/
def etaleLocalRingHom (j : U ⟶ X) [Etale j] (ubar : GeometricPoint U) :
    etaleLocalRing U ubar →+* etaleLocalRing X (ubar.map j) :=
  RingCat.Hom.hom <|
    (toSmallEtalePoint ubar).presheafFiberDesc
      (fun V l ↦
        (restrictStructurePresheafIso j).hom.app (op V) ≫
          (toSmallEtalePoint (ubar.map j)).toPresheafFiber ((restrictPostcompose j).obj V)
            (restrictPostcomposeLift j ubar l) (structureSheaf X).obj)
      (fun _ _ _ _ ↦ sorry)

/-- Opposite map of étale local rings `𝒪_{X, ubar.map j} →+* 𝒪_{U, ubar}`, obtained by
descending along the explicit fibre-product projection `etaleBaseChangeSnd`. -/
def etaleLocalRingInvHom (j : U ⟶ X) [Etale j] (ubar : GeometricPoint U) :
    etaleLocalRing X (ubar.map j) →+* etaleLocalRing U ubar :=
  RingCat.Hom.hom <|
    (toSmallEtalePoint (ubar.map j)).presheafFiberDesc
      (fun W l ↦
        (structureSheaf X).obj.map (op (restrictNeighborhoodRefineHom j ubar l)) ≫
          (restrictStructurePresheafIso j).inv.app
              (op (restrictNeighborhoodRefineObj j ubar l)) ≫
            (toSmallEtalePoint ubar).toPresheafFiber
              (restrictNeighborhoodRefineObj j ubar l)
              (restrictNeighborhoodRefineLift j ubar l) (structureSheaf U).obj)
      (fun _ _ _ _ ↦ sorry)

/-- The identity-on-sections local ring map is inverse to `etaleLocalRingInvHom`. -/
theorem etaleLocalRingHom_comp_inv (j : U ⟶ X) [Etale j] (ubar : GeometricPoint U) :
    (etaleLocalRingInvHom j ubar).comp (etaleLocalRingHom j ubar) =
      RingHom.id (etaleLocalRing U ubar) :=
  sorry

/-- The fibre-product local ring map is inverse to `etaleLocalRingHom`. -/
theorem etaleLocalRingInvHom_comp (j : U ⟶ X) [Etale j] (ubar : GeometricPoint U) :
    (etaleLocalRingHom j ubar).comp (etaleLocalRingInvHom j ubar) =
      RingHom.id (etaleLocalRing X (ubar.map j)) :=
  sorry

/-- For an étale morphism, the identity-on-sections map of étale local rings is an
isomorphism. -/
instance etaleLocalRingHom_isIso (j : U ⟶ X) [Etale j] (ubar : GeometricPoint U) :
    IsIso (RingCat.ofHom (etaleLocalRingHom j ubar)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {U X : AlgebraicSpace S}

/-- Underlying additive presheaf of étale restriction is postcomposition of the original
additive presheaf, via `restrictAppIso`. -/
def restrictPresheafAddIso (j : U ⟶ X) [Etale j] (F : X.Modules) :
    (restrict F j).val.presheaf ≅ (restrictPostcompose j).op ⋙ F.val.presheaf :=
  NatIso.ofComponents
    (fun V ↦ (forget₂ (ModuleCat _) AddCommGrpCat.{u}).mapIso (restrictAppIso F j V.unop))
    sorry

/-- Restriction of scalars along a ring homomorphism does not change the underlying additive
group. -/
def restrictScalars_forget₂Iso {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (M : ModuleCat.{u} S) :
    (forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u}).obj M ≅
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj ((restrictScalars f).obj M) :=
  Iso.refl _

/-- The additive group of an étale module stalk is the site-point fibre of the underlying
additive presheaf. -/
def moduleStalk_addIso {Z : AlgebraicSpace S} (xbar : GeometricPoint Z) (F : Z.Modules) :
    (forget₂ (ModuleCat (etaleLocalRing Z xbar)) AddCommGrpCat.{u}).obj
      (stalkModuleCat xbar F) ≅
      (toSmallEtalePoint xbar).presheafFiber.obj F.val.presheaf :=
  Iso.refl _

/-- Additive identity-on-sections comparison of restriction stalks, sending the germ of a
restricted section over `V` to the germ of the same section over the postcomposed
neighbourhood of `ubar.map j`. -/
def restrictStalkAddHom (j : U ⟶ X) [Etale j] (F : X.Modules) (ubar : GeometricPoint U) :
    (toSmallEtalePoint ubar).presheafFiber.obj (restrict F j).val.presheaf ⟶
      (toSmallEtalePoint (ubar.map j)).presheafFiber.obj F.val.presheaf :=
  (toSmallEtalePoint ubar).presheafFiberDesc
    (fun V l ↦
      (restrictPresheafAddIso j F).hom.app (op V) ≫
        (toSmallEtalePoint (ubar.map j)).toPresheafFiber ((restrictPostcompose j).obj V)
          (restrictPostcomposeLift j ubar l) F.val.presheaf)
    (fun _ _ _ _ ↦ sorry)

/-- Additive inverse comparison, obtained by descending along the explicit fibre-product
projection `etaleBaseChangeSnd`. -/
def restrictStalkAddInv (j : U ⟶ X) [Etale j] (F : X.Modules) (ubar : GeometricPoint U) :
    (toSmallEtalePoint (ubar.map j)).presheafFiber.obj F.val.presheaf ⟶
      (toSmallEtalePoint ubar).presheafFiber.obj (restrict F j).val.presheaf :=
  (toSmallEtalePoint (ubar.map j)).presheafFiberDesc
    (fun W l ↦
      F.val.presheaf.map (op (restrictNeighborhoodRefineHom j ubar l)) ≫
        (restrictPresheafAddIso j F).inv.app
            (op (restrictNeighborhoodRefineObj j ubar l)) ≫
          (toSmallEtalePoint ubar).toPresheafFiber
            (restrictNeighborhoodRefineObj j ubar l)
            (restrictNeighborhoodRefineLift j ubar l) (restrict F j).val.presheaf)
    (fun _ _ _ _ ↦ sorry)

/-- Additive identification of the étale restriction stalk with the ambient stalk. -/
def restrictStalkAddIso (j : U ⟶ X) [Etale j] (F : X.Modules) (ubar : GeometricPoint U) :
    (forget₂ (ModuleCat (etaleLocalRing U ubar)) AddCommGrpCat.{u}).obj
      (stalkModuleCat ubar (restrict F j)) ≅
      (forget₂ (ModuleCat (etaleLocalRing X (ubar.map j))) AddCommGrpCat.{u}).obj
        (stalkModuleCat (ubar.map j) F) where
  hom := (moduleStalk_addIso ubar (restrict F j)).hom ≫ restrictStalkAddHom j F ubar ≫
      (moduleStalk_addIso (ubar.map j) F).inv
  inv := (moduleStalk_addIso (ubar.map j) F).hom ≫ restrictStalkAddInv j F ubar ≫
      (moduleStalk_addIso ubar (restrict F j)).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Canonical identification `(restrict F j)_{ubar} ≅ F_{ubar.map j}` as modules over
`𝒪_{U, ubar}`, after transporting scalars along `etaleLocalRingHom`. -/
def restrictStalkIso (j : U ⟶ X) [Etale j] (F : X.Modules) (ubar : GeometricPoint U) :
    stalkModuleCat ubar (restrict F j) ≅
      (restrictScalars (etaleLocalRingHom j ubar)).obj (stalkModuleCat (ubar.map j) F) where
  hom :=
    homMk ((restrictStalkAddIso j F ubar).hom ≫
        (restrictScalars_forget₂Iso (etaleLocalRingHom j ubar)
          (stalkModuleCat (ubar.map j) F)).hom)
      sorry
  inv :=
    homMk ((restrictScalars_forget₂Iso (etaleLocalRingHom j ubar)
          (stalkModuleCat (ubar.map j) F)).inv ≫
        (restrictStalkAddIso j F ubar).inv)
      sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `restrictStalkIso` forgets to the additive comparison. -/
theorem restrictStalkIso_hom (j : U ⟶ X) [Etale j] (F : X.Modules)
    (ubar : GeometricPoint U) :
    (forget₂ (ModuleCat (etaleLocalRing U ubar)) AddCommGrpCat.{u}).map
        (restrictStalkIso j F ubar).hom =
      (restrictStalkAddIso j F ubar).hom ≫
        (restrictScalars_forget₂Iso (etaleLocalRingHom j ubar)
          (stalkModuleCat (ubar.map j) F)).hom :=
  sorry

/-- The inverse map of `restrictStalkIso` forgets to the inverse additive comparison. -/
theorem restrictStalkIso_inv (j : U ⟶ X) [Etale j] (F : X.Modules)
    (ubar : GeometricPoint U) :
    (forget₂ (ModuleCat (etaleLocalRing U ubar)) AddCommGrpCat.{u}).map
        (restrictStalkIso j F ubar).inv =
      (restrictScalars_forget₂Iso (etaleLocalRingHom j ubar)
          (stalkModuleCat (ubar.map j) F)).inv ≫
        (restrictStalkAddIso j F ubar).inv :=
  sorry

/-- Germs of restricted sections map to germs of the same sections on the postcomposed étale
neighbourhood. -/
theorem restrictStalkIso_germ (j : U ⟶ X) [Etale j] (F : X.Modules)
    (ubar : GeometricPoint U) (V : smallEtaleSite U) (l : OverLift ubar V) :
    (toSmallEtalePoint ubar).toPresheafFiber V l (restrict F j).val.presheaf ≫
        (restrictStalkAddIso j F ubar).hom =
      (restrictPresheafAddIso j F).hom.app (op V) ≫
        (toSmallEtalePoint (ubar.map j)).toPresheafFiber ((restrictPostcompose j).obj V)
          (restrictPostcomposeLift j ubar l) F.val.presheaf :=
  sorry

/-- `restrictStalkIso` is natural in the module sheaf. -/
theorem restrictStalkIso_natural (j : U ⟶ X) [Etale j] {F G : X.Modules}
    (φ : F ⟶ G) (ubar : GeometricPoint U) :
    ((toSmallEtalePoint ubar).sheafModuleStalkFunctor (structureSheaf U)).map
          ((restrictFunctor j).map φ) ≫
        (restrictStalkIso j G ubar).hom =
      (restrictStalkIso j F ubar).hom ≫
        (restrictScalars (etaleLocalRingHom j ubar)).map
          (((toSmallEtalePoint (ubar.map j)).sheafModuleStalkFunctor (structureSheaf X)).map φ) :=
  sorry

/-- Functorial form of `restrictStalkIso`, as a natural isomorphism of stalk functors. -/
def restrictStalkNatIso (j : U ⟶ X) [Etale j] (ubar : GeometricPoint U) :
    restrictFunctor j ⋙ (toSmallEtalePoint ubar).sheafModuleStalkFunctor (structureSheaf U) ≅
      (toSmallEtalePoint (ubar.map j)).sheafModuleStalkFunctor (structureSheaf X) ⋙
        restrictScalars (etaleLocalRingHom j ubar) :=
  NatIso.ofComponents (fun F ↦ restrictStalkIso j F ubar) sorry

/-- Components of `restrictStalkNatIso` are `restrictStalkIso`. -/
theorem restrictStalkNatIso_app (j : U ⟶ X) [Etale j] (ubar : GeometricPoint U)
    (F : X.Modules) :
    (restrictStalkNatIso j ubar).app F = restrictStalkIso j F ubar :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
