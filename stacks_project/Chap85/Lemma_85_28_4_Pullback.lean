/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.RingedSpace
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import stacks_project.Chap85.Definition_85_27_3_Nerve
public import stacks_project.Chap85.Lemma_85_28_1
public import stacks_project.Chap85.Lemma_85_28_4_QCoh

/-!
# Pullback of quasi-coherent modules along a Čech nerve

The augmentation of the Čech nerve of `f : X ⟶ S` is a morphism of simplicial
schemes `(X/S)_• ⟶ const S`. Combined with the degree-zero fibre comparison from
`S_Zar` to `(const S)_Zar`, it induces pullback
`Scheme.QCoh S ⥤ QCoh f.simplicialScheme`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialObject CategoryTheory.ObjectProperty
open Opposite AlgebraicGeometry TopologicalSpace TopCat RingedSite
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.SimplicialObject

/-- The constant simplicial scheme with value `S`. -/
abbrev constScheme (S : Scheme.{u}) : SimplicialObject Scheme.{u} :=
  (SimplicialObject.const Scheme.{u}).obj S

/-- The constant simplicial scheme evaluates to `S` in every degree. -/
theorem constScheme_obj (S : Scheme.{u}) (n : SimplexCategoryᵒᵖ) :
    (constScheme S).obj n = S :=
  sorry

/-- Degree-zero fibre inclusion of the constant simplicial Zariski site of `S`. -/
abbrev constFiber (S : Scheme.{u}) :
    RingedSpace.opensRingedSite S.toRingedSpace ⥤ zariskiRingedSite (constScheme S) :=
  DiagramOpens.fiber (forgetToTop.obj (constScheme S)) (op ⦋0⦌)

/-- The degree-zero fibre is continuous as a functor of sites from `S_Zar` to
`(const S)_Zar`. -/
instance constFiber_isContinuous (S : Scheme.{u}) :
    (constFiber S).IsContinuous
      (RingedSpace.opensRingedSite S.toRingedSpace).siteTopology
      (zariskiRingedSite (constScheme S)).siteTopology :=
  sorry

/-- The degree-zero fibre of the constant simplicial scheme of `S` is a morphism of
sites from `(const S)_Zar` to the opens site of `S`. -/
instance constFiber_isMorphismOfSites (S : Scheme.{u}) :
    IsMorphismOfSites
      (RingedSpace.opensRingedSite S.toRingedSpace).siteTopology
      (zariskiRingedSite (constScheme S)).siteTopology (constFiber S) :=
  sorry

/-- The component at an open of the adjoint structure-sheaf map of the constant
comparison. -/
def constRingedHom_structureSheafMap_app (S : Scheme.{u})
    (W : (RingedSpace.opensRingedSite S.toRingedSpace)ᵒᵖ) :
    (RingedSpace.opensRingedSite S.toRingedSpace).structureSheaf.obj.obj W ⟶
      (zariskiRingedSite (constScheme S)).structureSheaf.obj.obj
        (op ((constFiber S).obj W.unop)) :=
  𝟙 _

/-- The adjoint structure-sheaf map `𝒪_S ⟶ u_* 𝒪_{const S}` of the constant
comparison. -/
def constRingedHom_structureSheafMap (S : Scheme.{u}) :
    (RingedSpace.opensRingedSite S.toRingedSpace).structureSheaf ⟶
      ((constFiber S).sheafPushforwardContinuous RingCat.{u}
        (RingedSpace.opensRingedSite S.toRingedSpace).siteTopology
        (zariskiRingedSite (constScheme S)).siteTopology).obj
        (zariskiRingedSite (constScheme S)).structureSheaf :=
  ⟨{ app := fun W ↦ constRingedHom_structureSheafMap_app S W
     naturality := fun _ _ _ ↦ sorry }⟩

/-- The morphism of ringed sites `(const S)_Zar ⟶ S_Zar` induced by the degree-zero
fibre inclusion. -/
def constRingedHom (S : Scheme.{u}) :
    Hom (zariskiRingedSite (constScheme S))
      (RingedSpace.opensRingedSite S.toRingedSpace) where
  base := constFiber S
  structureSheafMap := constRingedHom_structureSheafMap S

/-- The underlying site functor of `constRingedHom S` is the degree-zero fibre. -/
theorem constRingedHom_base (S : Scheme.{u}) :
    (constRingedHom S).base = constFiber S :=
  sorry

/-- Module pushforward along `constRingedHom S` is a right adjoint, so module
pullback exists. -/
instance constRingedHom.modulePushforward_isRightAdjoint (S : Scheme.{u}) :
    ((constRingedHom S).modulePushforward.{u}).IsRightAdjoint :=
  sorry

/-- Pullback of modules from `S_Zar` to `(const S)_Zar`. -/
abbrev constModulePullback (S : Scheme.{u}) :=
  (constRingedHom S).modulePullback.{u}

/-- The augmentation `(X/S)_• ⟶ const S` of the Čech nerve of `f`. -/
def augmentation {X S : Scheme.{u}} (f : X ⟶ S) :
    f.simplicialScheme ⟶ constScheme S :=
  (Arrow.mk f).augmentedCechNerve.hom

/-- Components of the augmentation are the Čech-nerve base projections. -/
theorem augmentation_app {X S : Scheme.{u}} (f : X ⟶ S) (n : SimplexCategoryᵒᵖ) :
    (augmentation f).app n = Arrow.cechNerve.base (Arrow.mk f) n :=
  sorry

/-- Pullback of modules along a morphism of simplicial schemes preserves
quasi-coherence as an object property. -/
theorem modulePullback_le_inverseImage {V U : SimplicialObject Scheme.{u}}
    (f : V ⟶ U) :
    quasiCoherentModuleProperty U ≤
      (quasiCoherentModuleProperty V).inverseImage (modulePullback f) :=
  sorry

/-- Pullback of modules along `constRingedHom S` preserves quasi-coherence as an
object property. -/
theorem constPullback_le_inverseImage (S : Scheme.{u}) :
    RingedSpace.quasiCoherentModuleProperty S.toRingedSpace ≤
      (quasiCoherentModuleProperty (constScheme S)).inverseImage
        (constModulePullback S) :=
  sorry

namespace QCoh

/-- Restriction of `constModulePullback S` to quasi-coherent modules. -/
def constPullback (S : Scheme.{u}) :
    RingedSpace.QCoh S.toRingedSpace ⥤ QCoh (constScheme S) :=
  FullSubcategory.restrict (constModulePullback S) (constPullback_le_inverseImage S)

/-- Pullback of quasi-coherent modules along the Čech nerve of `f : X ⟶ S`. -/
def pullback {X S : Scheme.{u}} (f : X ⟶ S) :
    Scheme.QCoh S ⥤ QCoh f.simplicialScheme :=
  Scheme.QCoh.toRingedSpace S ⋙
    constPullback S ⋙
    FullSubcategory.restrict (modulePullback (augmentation f))
      (modulePullback_le_inverseImage (augmentation f))

/-- The underlying module sheaf of `QCoh.pullback f` is the composite of the
constant comparison with module pullback along the augmentation. -/
theorem pullback_obj {X S : Scheme.{u}} (f : X ⟶ S) (G : Scheme.QCoh S) :
    ((pullback f).obj G).obj =
      (modulePullback (augmentation f)).obj
        ((constModulePullback S).obj ((Scheme.Modules.toRingedSpace S).obj G.obj)) :=
  sorry

end QCoh

end AlgebraicGeometry.SimplicialObject
