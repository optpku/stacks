/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.Category.TopCat.OpenNhds
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Exact
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology.Map
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.PullbackStalk
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pushforward.Stalk
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition
public import ReasLib.Topology.Sheaf.Cohomology.Pushforward
public import ReasLib.Topology.Sheaf.HigherDirectImage.Presheaf
public import ReasLib.CategoryTheory.Sites.Cohomology.Zero
public import Mathlib.CategoryTheory.Sites.Sheafification
public import stacks_project.Chap30.Lemma_30_20_7_Tower

/-!
# Comparison from the completed higher-direct-image stalk to the neighbourhood tower

The maps `(R^p f_* ℱ)_y ⟶ H^p(X_{n+1}, ℱ_{n+1})` descend through `m_y^{n+1}`-annihilation
and assemble to a morphism from the `m_y`-adic completion to the inverse limit of the
neighbourhood cohomology tower in `𝒪_{Y,y}^∧`-modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ConcreteCategory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom.FiberNeighbourhood
open IsLocalRing
open TopologicalSpace TopologicalSpace.OpenNhds

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace FiberNeighbourhood

/-- Topological sheaf pushforward of abelian sheaves is additive. -/
instance sheafPushforward_additive {A B : TopCat.{u}} (g : A ⟶ B) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).Additive :=
  sorry

/-- The underlying-additive-sheaf functor is additive. -/
instance toSheafAdditive (Z : Scheme.{u}) :
    (SheafOfModules.toSheaf Z.ringCatSheaf).Additive :=
  sorry

/-- The underlying-additive-sheaf functor preserves homology. -/
instance toSheafPreservesHomology (Z : Scheme.{u}) :
    (SheafOfModules.toSheaf Z.ringCatSheaf).PreservesHomology :=
  sorry

/-- Additive sheaves on a scheme admit injective resolutions. -/
instance hasInjectiveResolutionsSheaf (Z : Scheme.{u}) :
    HasInjectiveResolutions
      (Sheaf (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}) :=
  sorry

/-- Underlying additive sheaf followed by topological pushforward is additive. -/
instance toSheafCompPushforward_additive {Z W : Scheme.{u}} (h : Z ⟶ W) :
    (SheafOfModules.toSheaf Z.ringCatSheaf ⋙
      TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.base).Additive :=
  sorry

/-- Exactness of `toSheaf` identifies deriving `toSheaf ⋙ pushforward` with the
topological higher direct image of the underlying additive sheaf. -/
theorem toSheafCompPushforwardRightDerived_obj_eq {Z W : Scheme.{u}} (h : Z ⟶ W) (p : ℕ)
    (G : Z.Modules) :
    ((SheafOfModules.toSheaf Z.ringCatSheaf ⋙
        TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.base).rightDerived p).obj G =
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.base).rightDerived p).obj
        ((SheafOfModules.toSheaf Z.ringCatSheaf).obj G) :=
  sorry

/-- Exactness of `toSheaf` compares `(toSheaf ⋙ pushforward).rightDerived p` with
`pushforward.rightDerived p` applied to `toSheaf.obj G`. -/
def toSheafCompPushforwardRightDerivedIso {Z W : Scheme.{u}} (h : Z ⟶ W) (p : ℕ)
    (G : Z.Modules) :
    ((SheafOfModules.toSheaf Z.ringCatSheaf ⋙
        TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.base).rightDerived p).obj G ≅
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.base).rightDerived p).obj
        ((SheafOfModules.toSheaf Z.ringCatSheaf).obj G) :=
  eqToIso (toSheafCompPushforwardRightDerived_obj_eq h p G)

section ComparisonData

variable {X Y : Scheme.{u}}

/-- The `m_y`-adic completion of the stalk `(R^p f_* ℱ)_y`. -/
abbrev completedStalk (f : X ⟶ Y) (F : X.Modules) (y : Y) (p : ℕ) : Type u :=
  AdicCompletion (maximalIdeal (Y.presheaf.stalk y))
    (RingedSpace.stalkModuleCat
      (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y)

/-- The completed stalk is the adic completion of the higher-direct-image stalk. -/
theorem completedStalk_eq (f : X ⟶ Y) (F : X.Modules) (y : Y) (p : ℕ) :
    completedStalk f F y p =
      AdicCompletion (maximalIdeal (Y.presheaf.stalk y))
        (RingedSpace.stalkModuleCat
          (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y) :=
  sorry

/-- The adjunction unit `ℱ ⟶ i_{n+1,*} i_{n+1}^* ℱ`. -/
def unitToPushed (f : X ⟶ Y) (F : X.Modules) (y : Y) (n : ℕ) :
    F ⟶ (Scheme.Modules.pushforward (ι f y n)).obj (sheaf f F y n) :=
  (Scheme.Modules.pullbackPushforwardAdjunction (ι f y n)).unit.app F

/-- The unit is the pullback–pushforward adjunction unit of `ι`. -/
theorem unitToPushed_eq (f : X ⟶ Y) (F : X.Modules) (y : Y) (n : ℕ) :
    unitToPushed f F y n =
      (Scheme.Modules.pullbackPushforwardAdjunction (ι f y n)).unit.app F :=
  sorry

/-- The induced map on stalks `(R^p f_* ℱ)_y ⟶ (R^p f_* i_{n+1,*} ℱ_{n+1})_y`. -/
def stalkToPushed (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    RingedSpace.stalkModuleCat
      (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y ⟶
      RingedSpace.stalkModuleCat
        (RingedSpace.Hom.higherDirectImageModule f.toShHom
          ((Scheme.Modules.pushforward (ι f y n)).obj (sheaf f F y n)) p) y :=
  (RingedSpace.stalkModuleFunctor y).map
    (RingedSpace.Hom.higherDirectImageModuleMap f.toShHom (unitToPushed f F y n) p)

/-- The quotient map `𝒪_{Y,y} ⟶ 𝒪_{Y,y} ⧸ m_y^{n+1}` is a local homomorphism. -/
instance isLocalHom_quotientMk (y : Y) (n : ℕ) :
    IsLocalHom
      (CommRingCat.ofHom
          (Ideal.Quotient.mk (maximalIdeal (Y.presheaf.stalk y) ^ (n + 1)))).hom :=
  sorry

/-- The sheaf of higher direct images of `ℱ_{n+1}` along `toSpec`. -/
abbrev specHigherDirectImage (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    (quotientSpec y n).Modules :=
  RingedSpace.Hom.higherDirectImageModule (toSpec f y n).toShHom (sheaf f F y n) p

/-- The neighbourhood square `ι ≫ f = toSpec ≫ toBase` as a commutative square of
ringed spaces. -/
theorem neighbourhoodCommSq (f : X ⟶ Y) (y : Y) (n : ℕ) :
    CommSq (ι f y n).toShHom (toSpec f y n).toShHom f.toShHom (toBase y n).toShHom :=
  ⟨(rfl : (ι f y n ≫ f).toShHom = (ι f y n).toShHom ≫ f.toShHom).symm.trans
    ((congrArg (fun φ : scheme f y n ⟶ Y ↦ φ.toShHom)
        (pullback.condition (f := f) (g := toBase y n))).trans
      (rfl : (toSpec f y n ≫ toBase y n).toShHom =
        (toSpec f y n).toShHom ≫ (toBase y n).toShHom))⟩

/-- Base change `toBase^* (R^p f_* ℱ) ⟶ R^p toSpec_* ℱ_{n+1}`. -/
def higherDirectImageBaseChange (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    (RingedSpace.Hom.pullback (toBase y n).toShHom).obj
        (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) ⟶
      specHigherDirectImage f F y p n :=
  RingedSpace.Hom.higherDirectImageModuleBaseChangeMap (neighbourhoodCommSq f y n)
    F p

/-- The closed point of `Spec(𝒪_{Y,y} ⧸ m_y^{n+1})` is sent to `y` by `toBase`. -/
theorem toBase_apply_closedPoint (y : Y) (n : ℕ) :
    toBase y n (closedPoint (quotientRing y n)) = y :=
  (rfl : toBase y n (closedPoint (quotientRing y n)) =
      (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (maximalIdeal (Y.presheaf.stalk y) ^ (n + 1)))) ≫
        Y.fromSpecStalk y)
        (closedPoint (quotientRing y n))).trans
    ((Scheme.Hom.comp_apply
        (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (maximalIdeal (Y.presheaf.stalk y) ^ (n + 1)))))
        (Y.fromSpecStalk y)
        (closedPoint (quotientRing y n))).trans
      ((congrArg (Y.fromSpecStalk y) (Spec_closedPoint
          (f := CommRingCat.ofHom
            (Ideal.Quotient.mk (maximalIdeal (Y.presheaf.stalk y) ^ (n + 1)))))).trans
        fromSpecStalk_closedPoint))

/-- Pullback of the higher direct image along `toBase`. -/
abbrev pullbackHigherDirectImage (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    (quotientSpec y n).Modules :=
  (RingedSpace.Hom.pullback (toBase y n).toShHom).obj
    (RingedSpace.Hom.higherDirectImageModule f.toShHom F p)

/-- The inverse of `Γgerm` at the closed point, sending a germ on any neighbourhood to the
corresponding global section via the identification of that neighbourhood with `⊤`. -/
def closedPointStalkToGamma (y : Y) (n : ℕ) (G : (quotientSpec y n).Modules) :
    TopCat.Presheaf.stalk G.val.presheaf (closedPoint (quotientRing y n)) ⟶
      G.val.presheaf.obj (op ⊤) :=
  let x : (quotientSpec y n) := closedPoint (quotientRing y n)
  colimit.desc ((OpenNhds.inclusion x).op ⋙ G.val.presheaf)
    { pt := G.val.presheaf.obj (op ⊤)
      ι :=
        { app := fun U ↦
            G.val.presheaf.map
              (eqToHom
                (congrArg (fun V : Opens (quotientSpec y n) ↦ Opposite.op V)
                  (Scheme.preimage_eq_top_of_closedPoint_mem (𝟙 (quotientSpec y n))
                    U.unop.2)))
          naturality := fun _ _ _ ↦ sorry } }

/-- On `Spec` of a local ring, the closed-point stalk of a module sheaf is identified with
global sections by `Γgerm` and `closedPointStalkToGamma`. -/
def closedPointStalkGammaIso (y : Y) (n : ℕ) (G : (quotientSpec y n).Modules) :
    TopCat.Presheaf.stalk G.val.presheaf (closedPoint (quotientRing y n)) ≅
      G.val.presheaf.obj (op ⊤) where
  hom := closedPointStalkToGamma y n G
  inv := TopCat.Presheaf.Γgerm G.val.presheaf (closedPoint (quotientRing y n))
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The additive comparison from the closed-point stalk of `toBase^* (R^p f_* ℱ)`
to global sections. -/
def pullbackStalkToGamma (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    TopCat.Presheaf.stalk
        (pullbackHigherDirectImage f F y p n).val.presheaf
        (closedPoint (quotientRing y n)) ⟶
      (pullbackHigherDirectImage f F y p n).val.presheaf.obj (op ⊤) :=
  (closedPointStalkGammaIso y n (pullbackHigherDirectImage f F y p n)).hom

/-- The stalk `𝒪_{Y,y}` acts on neighbourhood cohomology through the quotient map. -/
instance instModuleStalkHomCohomology
    (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    Module (Y.presheaf.stalk y) (homCohomology f F y p n) :=
  Module.compHom _ (Ideal.Quotient.mk (maximalIdeal (Y.presheaf.stalk y) ^ (n + 1)))

/-- The image of the closed point under the ringed-space morphism `toBase` is `y`. -/
theorem toBase_toShHom_apply_closedPoint (y : Y) (n : ℕ) :
    (toBase y n).toShHom.hom.base (closedPoint (quotientRing y n)) = y :=
  sorry

/-- Additive identification of the bundled higher-direct-image stalk with the
presheaf stalk. -/
theorem higherDirectImageStalk_eq (f : X ⟶ Y) (F : X.Modules) (y : Y) (p : ℕ) :
    (forget₂ (ModuleCat (Y.presheaf.stalk y)) AddCommGrpCat.{u}).obj
        (RingedSpace.stalkModuleCat
          (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y) =
      TopCat.Presheaf.stalk
        (RingedSpace.Hom.higherDirectImageModule f.toShHom F p).val.presheaf y :=
  sorry

/-- Additive presheaf morphism underlying `higherDirectImageBaseChange`. -/
def higherDirectImageBaseChangePresheaf
    (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    (pullbackHigherDirectImage f F y p n).val.presheaf ⟶
      (specHigherDirectImage f F y p n).val.presheaf :=
  (PresheafOfModules.toPresheaf (quotientSpec y n).ringCatSheaf.obj).map
    (higherDirectImageBaseChange f F y p n).val

/-- `higherDirectImageBaseChangePresheaf` is the additive presheaf map of
`higherDirectImageBaseChange`. -/
theorem higherDirectImageBaseChangePresheaf_eq
    (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    higherDirectImageBaseChangePresheaf f F y p n =
      (PresheafOfModules.toPresheaf (quotientSpec y n).ringCatSheaf.obj).map
        (higherDirectImageBaseChange f F y p n).val :=
  sorry

/-- The closed point of `Spec(𝒪_{Y,y} ⧸ m_y^{n+1})` as a scheme point. -/
def quotientClosedPoint (y : Y) (n : ℕ) : quotientSpec y n :=
  closedPoint (quotientRing y n)

/-- `quotientClosedPoint` is the closed point of the infinitesimal quotient spectrum. -/
theorem quotientClosedPoint_eq (y : Y) (n : ℕ) :
    quotientClosedPoint y n = closedPoint (quotientRing y n) :=
  sorry

/-- Base change of higher direct images induces a map of closed-point stalks. -/
def pullbackStalkToSpecStalk (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    TopCat.Presheaf.stalk
        (pullbackHigherDirectImage f F y p n).val.presheaf
        (quotientClosedPoint y n) ⟶
      TopCat.Presheaf.stalk
        (specHigherDirectImage f F y p n).val.presheaf
        (quotientClosedPoint y n) :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (quotientClosedPoint y n)).map
    (higherDirectImageBaseChangePresheaf f F y p n)

/-- `pullbackStalkToSpecStalk` is the stalk map of `higherDirectImageBaseChange`. -/
theorem pullbackStalkToSpecStalk_eq (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    pullbackStalkToSpecStalk f F y p n =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
          (quotientClosedPoint y n)).map
        (higherDirectImageBaseChangePresheaf f F y p n) :=
  sorry

/-- Infinitesimal quotient spectra inherit Ext-groups of abelian sheaves. -/
instance hasExt_quotientSpec (y : Y) (n : ℕ) :
    HasExt (Sheaf (Opens.grothendieckTopology (quotientSpec y n).carrier) AddCommGrpCat.{u}) :=
  sorry

end ComparisonData

section ComparisonIso

variable {X Y : Scheme.{u}}

/-- Functorial underlying-additive comparison for module pushforward along `toSpec`. -/
def specPushforwardToSheafNatIso (f : X ⟶ Y) (y : Y) (n : ℕ) :
    Scheme.Modules.pushforward (toSpec f y n) ⋙
        SheafOfModules.toSheaf (quotientSpec y n).ringCatSheaf ≅
      SheafOfModules.toSheaf (scheme f y n).ringCatSheaf ⋙
        TopCat.Sheaf.pushforward AddCommGrpCat.{u} (toSpec f y n).base :=
  modulePushforwardToSheafNatIso (toSpec f y n)

/-- Module pushforward followed by the underlying additive sheaf is additive. -/
instance pushforwardToSheaf_additive {Z W : Scheme.{u}} (h : Z ⟶ W) :
    (Scheme.Modules.pushforward h ⋙
      SheafOfModules.toSheaf W.ringCatSheaf).Additive :=
  sorry

/-- Underlying additive sheaf followed by topological pushforward is additive. -/
instance toSheafPushforward_additive {Z W : Scheme.{u}} (h : Z ⟶ W) :
    (SheafOfModules.toSheaf Z.ringCatSheaf ⋙
      TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.base).Additive :=
  toSheafCompPushforward_additive h

/-- Right derivation commutes with postcomposition by `toSheaf`. -/
def pushforwardToSheafRightDerivedIso {Z W : Scheme.{u}} (h : Z ⟶ W) (p : ℕ) :
    (Scheme.Modules.pushforward h ⋙
        SheafOfModules.toSheaf W.ringCatSheaf).rightDerived p ≅
      (Scheme.Modules.pushforward h).rightDerived p ⋙
        SheafOfModules.toSheaf W.ringCatSheaf :=
  @Functor.RightDerived.postcompIso _ _ _ _ _ _ _ _ _
    (Scheme.Modules.pushforward h) (SheafOfModules.toSheaf W.ringCatSheaf)
    inferInstance (toSheafAdditive W)
    (toSheafPreservesHomology W) inferInstance p

/-- Forgetful comparison between the module-valued higher direct image along `toSpec` and
the topological higher direct image of the underlying additive sheaf. -/
def higherDirectImageUnderlyingIso (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    (SheafOfModules.toSheaf (quotientSpec y n).ringCatSheaf).obj
        (specHigherDirectImage f F y p n) ≅
      TopCat.Sheaf.higherDirectImage (toSpec f y n).base
        ((SheafOfModules.toSheaf (scheme f y n).ringCatSheaf).obj (sheaf f F y n)) p where
  hom :=
    (pushforwardToSheafRightDerivedIso (toSpec f y n) p).inv.app (sheaf f F y n) ≫
      (@CategoryTheory.NatIso.rightDerived _ _ _ _ _ _ _
          (Scheme.Modules.pushforward (toSpec f y n) ⋙
            SheafOfModules.toSheaf (quotientSpec y n).ringCatSheaf)
          (SheafOfModules.toSheaf (scheme f y n).ringCatSheaf ⋙
            TopCat.Sheaf.pushforward AddCommGrpCat.{u} (toSpec f y n).base)
          (pushforwardToSheaf_additive (toSpec f y n))
          (toSheafPushforward_additive (toSpec f y n))
          (specPushforwardToSheafNatIso f y n) p).hom.app (sheaf f F y n) ≫
      (toSheafCompPushforwardRightDerivedIso (toSpec f y n) p (sheaf f F y n)).hom
  inv :=
    (toSheafCompPushforwardRightDerivedIso (toSpec f y n) p (sheaf f F y n)).inv ≫
      (@CategoryTheory.NatIso.rightDerived _ _ _ _ _ _ _
          (Scheme.Modules.pushforward (toSpec f y n) ⋙
            SheafOfModules.toSheaf (quotientSpec y n).ringCatSheaf)
          (SheafOfModules.toSheaf (scheme f y n).ringCatSheaf ⋙
            TopCat.Sheaf.pushforward AddCommGrpCat.{u} (toSpec f y n).base)
          (pushforwardToSheaf_additive (toSpec f y n))
          (toSheafPushforward_additive (toSpec f y n))
          (specPushforwardToSheafNatIso f y n) p).inv.app (sheaf f F y n) ≫
      (pushforwardToSheafRightDerivedIso (toSpec f y n) p).hom.app (sheaf f F y n)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Global-sections form of `higherDirectImageUnderlyingIso`. -/
def topologicalHigherDirectImageGammaIso (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    (TopCat.Sheaf.higherDirectImage (toSpec f y n).base
        ((SheafOfModules.toSheaf (scheme f y n).ringCatSheaf).obj (sheaf f F y n)) p).obj.obj
      (op ⊤) ≅
      (specHigherDirectImage f F y p n).val.presheaf.obj (op ⊤) where
  hom := (higherDirectImageUnderlyingIso f F y p n).inv.hom.app (op ⊤)
  inv := (higherDirectImageUnderlyingIso f F y p n).hom.hom.app (op ⊤)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Sheafification unit of the pushed cohomology presheaf, evaluated on the global open. -/
def toSheafifyTop (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (toSpec f y n).base).obj
        (((SheafOfModules.toSheaf (scheme f y n).ringCatSheaf).obj
          (sheaf f F y n)).cohomologyPresheaf p)).obj (op ⊤) ⟶
      (((TopCat.Sheaf.HigherDirectImage.Presheaf.sheafifiedCohomologyFunctor
          (toSpec f y n).base p).obj
        ((SheafOfModules.toSheaf (scheme f y n).ringCatSheaf).obj
          (sheaf f F y n))).obj.obj (op ⊤)) :=
  (CategoryTheory.toSheafify
      (Opens.grothendieckTopology (quotientSpec y n))
      ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (toSpec f y n).base).obj
        (((SheafOfModules.toSheaf (scheme f y n).ringCatSheaf).obj
          (sheaf f F y n)).cohomologyPresheaf p))).app (op ⊤)

/-- The pushed cohomology presheaf on an infinitesimal affine base is a sheaf. -/
theorem isSheaf_pushedCohomologyPresheaf (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    Presheaf.IsSheaf (Opens.grothendieckTopology (quotientSpec y n))
      ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (toSpec f y n).base).obj
        (((SheafOfModules.toSheaf (scheme f y n).ringCatSheaf).obj
          (sheaf f F y n)).cohomologyPresheaf p)) :=
  sorry

/-- Adjunction counit of sheafification, evaluated on the global open, after bundling the
pushed cohomology presheaf as a sheaf. -/
def fromSheafifyTop (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    (((TopCat.Sheaf.HigherDirectImage.Presheaf.sheafifiedCohomologyFunctor
          (toSpec f y n).base p).obj
        ((SheafOfModules.toSheaf (scheme f y n).ringCatSheaf).obj
          (sheaf f F y n))).obj.obj (op ⊤)) ⟶
      ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (toSpec f y n).base).obj
        (((SheafOfModules.toSheaf (scheme f y n).ringCatSheaf).obj
          (sheaf f F y n)).cohomologyPresheaf p)).obj (op ⊤) :=
  ((sheafificationAdjunction
        (Opens.grothendieckTopology (quotientSpec y n)) AddCommGrpCat.{u}).counit.app
      ⟨((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (toSpec f y n).base).obj
          (((SheafOfModules.toSheaf (scheme f y n).ringCatSheaf).obj
            (sheaf f F y n)).cohomologyPresheaf p)),
        isSheaf_pushedCohomologyPresheaf f F y p n⟩).hom.app (op ⊤)

/-- Affine sheafification-unit isomorphism on global sections of the pushed cohomology
presheaf. The inverse is the sheafification adjunction counit after an `IsSheaf` witness,
not `IsIso.inv`. -/
def sheafifyTopIso (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (toSpec f y n).base).obj
        (((SheafOfModules.toSheaf (scheme f y n).ringCatSheaf).obj
          (sheaf f F y n)).cohomologyPresheaf p)).obj (op ⊤) ≅
      (((TopCat.Sheaf.HigherDirectImage.Presheaf.sheafifiedCohomologyFunctor
          (toSpec f y n).base p).obj
        ((SheafOfModules.toSheaf (scheme f y n).ringCatSheaf).obj
          (sheaf f F y n))).obj.obj (op ⊤)) where
  hom := toSheafifyTop f F y p n
  inv := fromSheafifyTop f F y p n
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Affine Leray edge from neighbourhood cohomology to global sections of
`R^p toSpec_* ℱ_{n+1}`. -/
def homCohomologyToGamma (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    (forget₂ (ModuleCat (quotientRing y n)) AddCommGrpCat.{u}).obj
        (homCohomology f F y p n) ⟶
      (specHigherDirectImage f F y p n).val.presheaf.obj (op ⊤) :=
  homCohomologyToSheaf f F y p n ≫
    eqToHom
      (congrArg
        (fun U : Opens (scheme f y n) ↦
          ((SheafOfModules.toSheaf (scheme f y n).ringCatSheaf).obj (sheaf f F y n)).H' p U)
        (Opens.map_top (toSpec f y n).base).symm) ≫
    (sheafifyTopIso f F y p n).hom ≫
    (TopCat.Sheaf.HigherDirectImage.Presheaf.objIso (toSpec f y n).base
        ((SheafOfModules.toSheaf (scheme f y n).ringCatSheaf).obj (sheaf f F y n)) p).hom.hom.app
      (op ⊤) ≫
    (topologicalHigherDirectImageGammaIso f F y p n).hom

/-- Inverse affine Leray edge from global sections of `R^p toSpec_* ℱ_{n+1}` to
neighbourhood cohomology. -/
def gammaToHomCohomology (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    (specHigherDirectImage f F y p n).val.presheaf.obj (op ⊤) ⟶
      (forget₂ (ModuleCat (quotientRing y n)) AddCommGrpCat.{u}).obj
        (homCohomology f F y p n) :=
  (topologicalHigherDirectImageGammaIso f F y p n).inv ≫
    (TopCat.Sheaf.HigherDirectImage.Presheaf.objIso (toSpec f y n).base
        ((SheafOfModules.toSheaf (scheme f y n).ringCatSheaf).obj (sheaf f F y n)) p).inv.hom.app
      (op ⊤) ≫
    (sheafifyTopIso f F y p n).inv ≫
    eqToHom
      (congrArg
        (fun U : Opens (scheme f y n) ↦
          ((SheafOfModules.toSheaf (scheme f y n).ringCatSheaf).obj (sheaf f F y n)).H' p U)
        (Opens.map_top (toSpec f y n).base)) ≫
    sheafToHomCohomology f F y p n

/-- Canonical isomorphism identifying global sections of `R^p toSpec_* ℱ_{n+1}` with
neighbourhood cohomology. This is the affine Leray edge, not a definitional equality. -/
def specHigherDirectImageGammaIso (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    (specHigherDirectImage f F y p n).val.presheaf.obj (op ⊤) ≅
      (forget₂ (ModuleCat (quotientRing y n)) AddCommGrpCat.{u}).obj
        (homCohomology f F y p n) where
  hom := gammaToHomCohomology f F y p n
  inv := homCohomologyToGamma f F y p n
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The underlying function of `toHomCohomology`. -/
def toHomCohomologyFun (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    RingedSpace.stalkModuleCat
      (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y →
      homCohomology f F y p n :=
  fun m ↦
    (specHigherDirectImageGammaIso f F y p n).hom
      ((closedPointStalkGammaIso y n (specHigherDirectImage f F y p n)).hom
        ((pullbackStalkToSpecStalk f F y p n).hom
          ((RingedSpace.Hom.pullbackStalkUnitHom (toBase y n).toShHom
              (RingedSpace.Hom.higherDirectImageModule f.toShHom F p)
              (closedPoint (quotientRing y n))).hom
            ((eqToHom
                (congrArg
                  (fun z : Y ↦
                    TopCat.Presheaf.stalk
                      (RingedSpace.Hom.higherDirectImageModule
                        f.toShHom F p).val.presheaf
                      z)
                  (toBase_toShHom_apply_closedPoint y n).symm)).hom
              ((eqToHom (higherDirectImageStalk_eq f F y p)).hom m)))))

/-- The underlying function of `toHomCohomology` is linear over `𝒪_{Y,y}`. -/
theorem isLinearMap_toHomCohomologyFun (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    IsLinearMap (Y.presheaf.stalk y) (toHomCohomologyFun f F y p n) :=
  sorry

/-- The comparison from the higher-direct-image stalk to neighbourhood cohomology is
semilinear along the quotient map `𝒪_{Y,y} ⟶ 𝒪_{Y,y} ⧸ m_y^{n+1}`. -/
def toHomCohomologySemilinear (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    RingedSpace.stalkModuleCat
        (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y →ₛₗ[
          Ideal.Quotient.mk (maximalIdeal (Y.presheaf.stalk y) ^ (n + 1))]
      (homCohomology f F y p n) where
  toFun := toHomCohomologyFun f F y p n
  map_add' := sorry
  map_smul' := sorry

/-- The canonical map from the higher-direct-image stalk to neighbourhood cohomology as an
`𝒪_{Y,y}`-module. -/
def toHomCohomology (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    RingedSpace.stalkModuleCat
      (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y ⟶
      (ModuleCat.restrictScalars
        (Ideal.Quotient.mk (maximalIdeal (Y.presheaf.stalk y) ^ (n + 1)))).obj
        (homCohomology f F y p n) :=
  ModuleCat.semilinearMapAddEquiv
      (Ideal.Quotient.mk (maximalIdeal (Y.presheaf.stalk y) ^ (n + 1)))
      (RingedSpace.stalkModuleCat
        (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y)
      (homCohomology f F y p n)
    (toHomCohomologySemilinear f F y p n)

/-- `m_y^{n+1}` annihilates the image of `toHomCohomology`. -/
theorem pow_smul_le_ker_toHomCohomology (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    maximalIdeal (Y.presheaf.stalk y) ^ (n + 1) •
        (⊤ : Submodule (Y.presheaf.stalk y)
          (RingedSpace.stalkModuleCat
            (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y)) ≤
      LinearMap.ker (toHomCohomology f F y p n).hom :=
  sorry

/-- The descended comparison
`(R^p f_* ℱ)_y ⧸ m_y^{n+1} • ⊤ ⟶ H^p(X_{n+1}, ℱ_{n+1})`. -/
def toHomCohomologyModPow (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    ModuleCat.of (Y.presheaf.stalk y)
      (RingedSpace.stalkModuleCat
          (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y ⧸
        maximalIdeal (Y.presheaf.stalk y) ^ (n + 1) •
          (⊤ : Submodule (Y.presheaf.stalk y)
            (RingedSpace.stalkModuleCat
              (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y))) ⟶
      (ModuleCat.restrictScalars
        (Ideal.Quotient.mk (maximalIdeal (Y.presheaf.stalk y) ^ (n + 1)))).obj
        (homCohomology f F y p n) :=
  ConcreteCategory.ofHom
    ((maximalIdeal (Y.presheaf.stalk y) ^ (n + 1) •
        (⊤ : Submodule (Y.presheaf.stalk y)
          (RingedSpace.stalkModuleCat
            (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y))).liftQ
      (toHomCohomology f F y p n).hom (pow_smul_le_ker_toHomCohomology f F y p n))

/-- The underlying function of the completed-stalk comparison at stage `n`. -/
def toStageFun (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    completedStalk f F y p → cohomology f F y p n :=
  fun x ↦
    (toHomCohomologyModPow f F y p n).hom
      (AdicCompletion.eval (maximalIdeal (Y.presheaf.stalk y))
        (RingedSpace.stalkModuleCat
          (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y)
        (n + 1) x)

/-- The underlying function of `toStage` is linear over `𝒪_{Y,y}^∧`. -/
theorem isLinearMap_toStageFun (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    IsLinearMap (completedRing y) (toStageFun f F y p n) :=
  sorry

/-- The stage map from the completed stalk to neighbourhood cohomology, as
`𝒪_{Y,y}^∧`-modules. -/
def toStage (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    ModuleCat.of (completedRing y) (completedStalk f F y p) ⟶ cohomology f F y p n :=
  ConcreteCategory.ofHom
    (IsLinearMap.mk' (toStageFun f F y p n) (isLinearMap_toStageFun f F y p n))

/-- Stage maps from the completed stalk are natural with respect to the cohomology tower. -/
theorem toStage_natural (f : X ⟶ Y) (F : X.Modules) (y : Y) (p : ℕ) (n : ℕ) :
    toStage f F y p (n + 1) ≫ cohomologyStep f F y p n = toStage f F y p n :=
  sorry

/-- The induced map from the completed higher-direct-image stalk to the inverse
limit of neighbourhood cohomology. -/
def limitComparison (f : X ⟶ Y) (F : X.Modules) (y : Y) (p : ℕ) :
    ModuleCat.of (completedRing y) (completedStalk f F y p) ⟶ limit (tower f F y p) :=
  limit.lift (tower f F y p)
    { pt := ModuleCat.of (completedRing y) (completedStalk f F y p)
      π :=
        { app := fun n ↦ toStage f F y p n.unop
          naturality := fun _ _ _ ↦ sorry } }

/-- Projecting `limitComparison` to stage `n` recovers `toStage`. -/
theorem limitComparison_comp_π (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    limitComparison f F y p ≫ limit.π (tower f F y p) (op n) = toStage f F y p n :=
  sorry

end ComparisonIso

end FiberNeighbourhood
end AlgebraicGeometry.Scheme.Hom
