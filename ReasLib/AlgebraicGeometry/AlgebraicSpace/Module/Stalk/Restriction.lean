module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PresentationRestriction

/-!
# Stalks of étale restriction of modules on algebraic spaces

Restriction along an étale morphism identifies module stalks at a geometric point and its
image, with scalar transport along the canonical map of étale local rings.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open ModuleCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {U X : AlgebraicSpace S}

/-- Underlying additive presheaf of étale restriction is postcomposition of the original
additive presheaf, via `restrictAppIso`. -/
def restrictPresheafAddIso (j : U ⟶ X) [Etale j] (F : X.Modules) :
    (restrict F j).val.presheaf ≅ (etaleRestriction j).op ⋙ F.val.presheaf :=
  NatIso.ofComponents
    (fun V ↦ (forget₂ (ModuleCat _) AddCommGrpCat.{u}).mapIso (restrictAppIso F j V.unop))
    sorry

/-- Additive identity-on-sections comparison of restriction stalks, sending the germ of a
restricted section over `V` to the germ of the same section over the postcomposed
neighbourhood of `ubar.map j`. -/
def restrictStalkAddHom (j : U ⟶ X) [Etale j] (F : X.Modules) (ubar : GeometricPoint U) :
    (toSmallEtalePoint ubar).presheafFiber.obj (restrict F j).val.presheaf ⟶
      (toSmallEtalePoint (ubar.map j)).presheafFiber.obj F.val.presheaf :=
  (toSmallEtalePoint ubar).presheafFiberDesc
    (fun V l ↦
      (restrictPresheafAddIso j F).hom.app (op V) ≫
        (toSmallEtalePoint (ubar.map j)).toPresheafFiber ((etaleRestriction j).obj V)
          (restrictPostcomposeLift j ubar l) F.val.presheaf)
    (fun _ _ _ _ ↦ sorry)

/-- Additive inverse comparison, obtained by descending along the scheme projection of the
represented atlas refinement. -/
def restrictStalkAddInv (j : U ⟶ X) [Etale j] (F : X.Modules) (ubar : GeometricPoint U) :
    (toSmallEtalePoint (ubar.map j)).presheafFiber.obj F.val.presheaf ⟶
      (toSmallEtalePoint ubar).presheafFiber.obj (restrict F j).val.presheaf :=
  (toSmallEtalePoint (ubar.map j)).presheafFiberDesc
    (fun W l ↦
      F.val.presheaf.map (op (restrictRefinementHom j W)) ≫
        (restrictPresheafAddIso j F).inv.app
            (op (restrictRefinementObj j W)) ≫
          (toSmallEtalePoint ubar).toPresheafFiber
            (restrictRefinementObj j W)
            (restrictRefinementLift j ubar l) (restrict F j).val.presheaf)
    (fun _ _ _ _ ↦ sorry)

/-- Additive identification of the étale restriction stalk with the ambient stalk. -/
def restrictStalkAddIso (j : U ⟶ X) [Etale j] (F : X.Modules) (ubar : GeometricPoint U) :
    (forget₂ (ModuleCat (etaleLocalRing U ubar)) AddCommGrpCat.{u}).obj
      (stalkModuleCat ubar (restrict F j)) ≅
      (forget₂ (ModuleCat (etaleLocalRing X (ubar.map j))) AddCommGrpCat.{u}).obj
        (stalkModuleCat (ubar.map j) F) where
  hom := restrictStalkAddHom j F ubar
  inv := restrictStalkAddInv j F ubar
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Canonical identification `(restrict F j)_{ubar} ≅ F_{ubar.map j}` as modules over
`𝒪_{U, ubar}`, after transporting scalars along `etaleLocalRingHom`. -/
def restrictStalkIso (j : U ⟶ X) [Etale j] (F : X.Modules) (ubar : GeometricPoint U) :
    stalkModuleCat ubar (restrict F j) ≅
      (restrictScalars (etaleLocalRingHom j ubar)).obj (stalkModuleCat (ubar.map j) F) where
  hom := homMk (restrictStalkAddIso j F ubar).hom sorry
  inv := homMk (restrictStalkAddIso j F ubar).inv sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `restrictStalkIso` forgets to the additive comparison. -/
theorem restrictStalkIso_hom (j : U ⟶ X) [Etale j] (F : X.Modules)
    (ubar : GeometricPoint U) :
    (forget₂ (ModuleCat (etaleLocalRing U ubar)) AddCommGrpCat.{u}).map
        (restrictStalkIso j F ubar).hom =
      (restrictStalkAddIso j F ubar).hom :=
  sorry

/-- The inverse map of `restrictStalkIso` forgets to the inverse additive comparison. -/
theorem restrictStalkIso_inv (j : U ⟶ X) [Etale j] (F : X.Modules)
    (ubar : GeometricPoint U) :
    (forget₂ (ModuleCat (etaleLocalRing U ubar)) AddCommGrpCat.{u}).map
        (restrictStalkIso j F ubar).inv =
      (restrictStalkAddIso j F ubar).inv :=
  sorry

/-- Germs of restricted sections map to germs of the same sections on the postcomposed étale
neighbourhood. -/
theorem restrictStalkIso_germ (j : U ⟶ X) [Etale j] (F : X.Modules)
    (ubar : GeometricPoint U) (V : smallEtaleSite U) (l : OverLift ubar V) :
    (toSmallEtalePoint ubar).toPresheafFiber V l (restrict F j).val.presheaf ≫
        (restrictStalkAddIso j F ubar).hom =
      (restrictPresheafAddIso j F).hom.app (op V) ≫
        (toSmallEtalePoint (ubar.map j)).toPresheafFiber ((etaleRestriction j).obj V)
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
