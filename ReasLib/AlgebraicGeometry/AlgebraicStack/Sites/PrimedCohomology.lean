module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.CategoryTheory.Sites.CostructuredArrowTopology
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.AbelianPushforward
public import ReasLib.CategoryTheory.Sites.AbelianSheaf
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive

/-!
# Primed comma sites and the higher-direct-image cohomology presheaf

For `f : X ⟶ Y` smooth (resp. flat) and `y` in the lisse-étale (resp. flat-fppf)
site of `Y`, the primed fibre product `(V ×_{y, Y} X)'` is the costructured
arrow category of the restricted site functor at `y`. The cohomology presheaf
sends `y` to global cohomology of `(pr')⁻¹ H` on that primed site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Abelian CategoryTheory.Limits
open Opposite
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]

/-- The primed fibre product `(V ×_{y, Y} X)'` of a lisse-étale object `y` along
a smooth morphism `f`. -/
abbrev lisseEtalePrimedSite (f : X ⟶ Y) [Smooth f] (y : lisseEtaleSite Y) :=
  CostructuredArrow (lisseEtaleMap f) y

/-- The projection `pr'` from `(V ×_{y, Y} X)'` to the lisse-étale site of `X`. -/
abbrev lisseEtalePrimedPr (f : X ⟶ Y) [Smooth f] (y : lisseEtaleSite Y) :
    lisseEtalePrimedSite f y ⥤ lisseEtaleSite X :=
  CostructuredArrow.proj (lisseEtaleMap f) y

/-- The Grothendieck topology on `(V ×_{y, Y} X)'` detected by `pr'`. -/
abbrev lisseEtalePrimedTopology (f : X ⟶ Y) [Smooth f] (y : lisseEtaleSite Y) :
    GrothendieckTopology (lisseEtalePrimedSite f y) :=
  cocontinuousOverTopology (lisseEtaleTopology X) (lisseEtaleMap f) y

/-- The pullback of an abelian sheaf along `pr'` to the primed lisse-étale
fibre product. -/
abbrev lisseEtalePrimedPullback (f : X ⟶ Y) [Smooth f] (y : lisseEtaleSite Y)
    (H : Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1}) :
    Sheaf (lisseEtalePrimedTopology f y) AddCommGrpCat.{u + 1} :=
  ((lisseEtalePrimedPr f y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (lisseEtalePrimedTopology f y) (lisseEtaleTopology X)).obj H

/-- The primed fibre product `(V ×_{y, Y} X)'` of a flat-fppf object `y` along a
flat morphism `f`. -/
abbrev flatFppfPrimedSite (f : X ⟶ Y) [Flat f] (y : flatFppfSite Y) :=
  CostructuredArrow (flatFppfMap f) y

/-- The projection `pr'` from `(V ×_{y, Y} X)'` to the flat-fppf site of `X`. -/
abbrev flatFppfPrimedPr (f : X ⟶ Y) [Flat f] (y : flatFppfSite Y) :
    flatFppfPrimedSite f y ⥤ flatFppfSite X :=
  CostructuredArrow.proj (flatFppfMap f) y

/-- The Grothendieck topology on the primed flat-fppf fibre product. -/
abbrev flatFppfPrimedTopology (f : X ⟶ Y) [Flat f] (y : flatFppfSite Y) :
    GrothendieckTopology (flatFppfPrimedSite f y) :=
  cocontinuousOverTopology (flatFppfTopology X) (flatFppfMap f) y

/-- The pullback of an abelian sheaf along `pr'` to the primed flat-fppf fibre
product. -/
abbrev flatFppfPrimedPullback (f : X ⟶ Y) [Flat f] (y : flatFppfSite Y)
    (H : Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1}) :
    Sheaf (flatFppfPrimedTopology f y) AddCommGrpCat.{u + 1} :=
  ((flatFppfPrimedPr f y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (flatFppfPrimedTopology f y) (flatFppfTopology X)).obj H

/-- Ext-groups of abelian sheaves on a primed lisse-étale fibre product land in
universe `u + 1`. -/
instance lisseEtalePrimedTopology.instHasExt
    (f : X ⟶ Y) [Smooth f] (y : lisseEtaleSite Y) :
    HasExt.{u + 1} (Sheaf (lisseEtalePrimedTopology f y) AddCommGrpCat.{u + 1}) :=
  sorry

/-- Ext-groups of abelian sheaves on a primed flat-fppf fibre product land in
universe `u + 1`. -/
instance flatFppfPrimedTopology.instHasExt
    (f : X ⟶ Y) [Flat f] (y : flatFppfSite Y) :
    HasExt.{u + 1} (Sheaf (flatFppfPrimedTopology f y) AddCommGrpCat.{u + 1}) :=
  sorry

/-- A morphism of lisse-étale objects induces a continuous functor of primed
fibre products. -/
instance lisseEtalePrimedMap.instIsContinuous
    (f : X ⟶ Y) [Smooth f] {y y' : lisseEtaleSite Y} (φ : y ⟶ y') :
    (CostructuredArrow.map φ).IsContinuous
      (lisseEtalePrimedTopology f y) (lisseEtalePrimedTopology f y') :=
  sorry

/-- A morphism of lisse-étale objects induces a cocontinuous functor of primed
fibre products. -/
instance lisseEtalePrimedMap.instIsCocontinuous
    (f : X ⟶ Y) [Smooth f] {y y' : lisseEtaleSite Y} (φ : y ⟶ y') :
    (CostructuredArrow.map φ).IsCocontinuous
      (lisseEtalePrimedTopology f y) (lisseEtalePrimedTopology f y') :=
  sorry

/-- A morphism of flat-fppf objects induces a continuous functor of primed fibre
products. -/
instance flatFppfPrimedMap.instIsContinuous
    (f : X ⟶ Y) [Flat f] {y y' : flatFppfSite Y} (φ : y ⟶ y') :
    (CostructuredArrow.map φ).IsContinuous
      (flatFppfPrimedTopology f y) (flatFppfPrimedTopology f y') :=
  sorry

/-- A morphism of flat-fppf objects induces a cocontinuous functor of primed
fibre products. -/
instance flatFppfPrimedMap.instIsCocontinuous
    (f : X ⟶ Y) [Flat f] {y y' : flatFppfSite Y} (φ : y ⟶ y') :
    (CostructuredArrow.map φ).IsCocontinuous
      (flatFppfPrimedTopology f y) (flatFppfPrimedTopology f y') :=
  sorry

/-- Pointwise right Kan extensions along the opposite of a primed lisse-étale
comparison exist on abelian presheaves. -/
instance lisseEtalePrimedMap.instHasPointwiseRightKanExtension
    (f : X ⟶ Y) [Smooth f] {y y' : lisseEtaleSite Y} (φ : y ⟶ y')
    (P : (lisseEtalePrimedSite f y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (CostructuredArrow.map φ).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Pointwise right Kan extensions along the opposite of a primed flat-fppf
comparison exist on abelian presheaves. -/
instance flatFppfPrimedMap.instHasPointwiseRightKanExtension
    (f : X ⟶ Y) [Flat f] {y y' : flatFppfSite Y} (φ : y ⟶ y')
    (P : (flatFppfPrimedSite f y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (CostructuredArrow.map φ).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Continuous pushforward along a primed lisse-étale comparison preserves finite
limits. -/
instance lisseEtalePrimedMap.instSheafPushforwardContinuousPreservesFiniteLimits
    (f : X ⟶ Y) [Smooth f] {y y' : lisseEtaleSite Y} (φ : y ⟶ y') :
    PreservesFiniteLimits
      ((CostructuredArrow.map φ).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (lisseEtalePrimedTopology f y) (lisseEtalePrimedTopology f y')) :=
  sorry

/-- Continuous pushforward along a primed lisse-étale comparison preserves finite
colimits. -/
instance lisseEtalePrimedMap.instSheafPushforwardContinuousPreservesFiniteColimits
    (f : X ⟶ Y) [Smooth f] {y y' : lisseEtaleSite Y} (φ : y ⟶ y') :
    PreservesFiniteColimits
      ((CostructuredArrow.map φ).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (lisseEtalePrimedTopology f y) (lisseEtalePrimedTopology f y')) :=
  sorry

/-- Continuous pushforward along a primed flat-fppf comparison preserves finite
limits. -/
instance flatFppfPrimedMap.instSheafPushforwardContinuousPreservesFiniteLimits
    (f : X ⟶ Y) [Flat f] {y y' : flatFppfSite Y} (φ : y ⟶ y') :
    PreservesFiniteLimits
      ((CostructuredArrow.map φ).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (flatFppfPrimedTopology f y) (flatFppfPrimedTopology f y')) :=
  sorry

/-- Continuous pushforward along a primed flat-fppf comparison preserves finite
colimits. -/
instance flatFppfPrimedMap.instSheafPushforwardContinuousPreservesFiniteColimits
    (f : X ⟶ Y) [Flat f] {y y' : flatFppfSite Y} (φ : y ⟶ y') :
    PreservesFiniteColimits
      ((CostructuredArrow.map φ).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (flatFppfPrimedTopology f y) (flatFppfPrimedTopology f y')) :=
  sorry

/-- Composing `CostructuredArrow.map φ` with `pr'` at the target recovers `pr'`
at the source. -/
def lisseEtalePrimedPr_comp_map (f : X ⟶ Y) [Smooth f]
    {y y' : lisseEtaleSite Y} (φ : y ⟶ y') :
    CostructuredArrow.map φ ⋙ lisseEtalePrimedPr f y' ≅ lisseEtalePrimedPr f y :=
  Iso.refl _

/-- Composing `CostructuredArrow.map φ` with `pr'` at the target recovers `pr'`
at the source. -/
def flatFppfPrimedPr_comp_map (f : X ⟶ Y) [Flat f]
    {y y' : flatFppfSite Y} (φ : y ⟶ y') :
    CostructuredArrow.map φ ⋙ flatFppfPrimedPr f y' ≅ flatFppfPrimedPr f y :=
  Iso.refl _

/-- Pulling `(pr')⁻¹ H` back along `CostructuredArrow.map φ` recovers the primed
pullback at the source object. -/
def lisseEtalePrimedPullbackMapIso (f : X ⟶ Y) [Smooth f]
    {y y' : lisseEtaleSite Y} (φ : y ⟶ y')
    (H : Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1}) :
    ((CostructuredArrow.map φ).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (lisseEtalePrimedTopology f y) (lisseEtalePrimedTopology f y')).obj
      (lisseEtalePrimedPullback f y' H) ≅
      lisseEtalePrimedPullback f y H :=
  (Functor.sheafPushforwardContinuousComp' (lisseEtalePrimedPr_comp_map f φ)
      AddCommGrpCat.{u + 1} (lisseEtalePrimedTopology f y)
      (lisseEtalePrimedTopology f y') (lisseEtaleTopology X)).app H

/-- Pulling `(pr')⁻¹ H` back along `CostructuredArrow.map φ` recovers the primed
pullback at the source object. -/
def flatFppfPrimedPullbackMapIso (f : X ⟶ Y) [Flat f]
    {y y' : flatFppfSite Y} (φ : y ⟶ y')
    (H : Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1}) :
    ((CostructuredArrow.map φ).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (flatFppfPrimedTopology f y) (flatFppfPrimedTopology f y')).obj
      (flatFppfPrimedPullback f y' H) ≅
      flatFppfPrimedPullback f y H :=
  (Functor.sheafPushforwardContinuousComp' (flatFppfPrimedPr_comp_map f φ)
      AddCommGrpCat.{u + 1} (flatFppfPrimedTopology f y)
      (flatFppfPrimedTopology f y') (flatFppfTopology X)).app H

/-- The constant sheaf of integers is preserved by primed lisse-étale
comparison functors. -/
def lisseEtalePrimedConstantPullbackIso (f : X ⟶ Y) [Smooth f]
    {y y' : lisseEtaleSite Y} (φ : y ⟶ y') :
    ((CostructuredArrow.map φ).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (lisseEtalePrimedTopology f y) (lisseEtalePrimedTopology f y')).obj
      ((constantSheaf (lisseEtalePrimedTopology f y') AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ))) ≅
      (constantSheaf (lisseEtalePrimedTopology f y) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) :=
  ((Functor.pushforwardContinuousSheafificationCompatibility (CostructuredArrow.map φ)
        AddCommGrpCat.{u + 1} (lisseEtalePrimedTopology f y)
        (lisseEtalePrimedTopology f y')).app
      ((Functor.const _).obj (AddCommGrpCat.of (ULift ℤ)))).symm ≪≫
    (presheafToSheaf (lisseEtalePrimedTopology f y) AddCommGrpCat.{u + 1}).mapIso
      ((Functor.constCompWhiskeringLeftIso
          (lisseEtalePrimedSite f y)ᵒᵖ (CostructuredArrow.map φ).op).app
        (AddCommGrpCat.of (ULift ℤ)))

/-- The constant sheaf of integers is preserved by primed flat-fppf comparison
functors. -/
def flatFppfPrimedConstantPullbackIso (f : X ⟶ Y) [Flat f]
    {y y' : flatFppfSite Y} (φ : y ⟶ y') :
    ((CostructuredArrow.map φ).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (flatFppfPrimedTopology f y) (flatFppfPrimedTopology f y')).obj
      ((constantSheaf (flatFppfPrimedTopology f y') AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ))) ≅
      (constantSheaf (flatFppfPrimedTopology f y) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) :=
  ((Functor.pushforwardContinuousSheafificationCompatibility (CostructuredArrow.map φ)
        AddCommGrpCat.{u + 1} (flatFppfPrimedTopology f y)
        (flatFppfPrimedTopology f y')).app
      ((Functor.const _).obj (AddCommGrpCat.of (ULift ℤ)))).symm ≪≫
    (presheafToSheaf (flatFppfPrimedTopology f y) AddCommGrpCat.{u + 1}).mapIso
      ((Functor.constCompWhiskeringLeftIso
          (flatFppfPrimedSite f y)ᵒᵖ (CostructuredArrow.map φ).op).app
        (AddCommGrpCat.of (ULift ℤ)))

/-- Restriction of primed-site cohomology along a morphism of lisse-étale
objects. -/
def lisseEtalePrimedCohomologyMap (f : X ⟶ Y) [Smooth f]
    {y y' : lisseEtaleSite Y} (φ : y ⟶ y')
    (H : Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1}) (p : ℕ) :
    ((lisseEtalePrimedPullback f y' H).H p) →+
      ((lisseEtalePrimedPullback f y H).H p) :=
  let Gu :=
    (CostructuredArrow.map φ).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (lisseEtalePrimedTopology f y) (lisseEtalePrimedTopology f y')
  ((Ext.mk₀ (lisseEtalePrimedConstantPullbackIso f φ).inv).precomp
      (lisseEtalePrimedPullback f y H) (zero_add p)).comp
    (((Ext.mk₀ (lisseEtalePrimedPullbackMapIso f φ H).hom).postcomp
        (Gu.obj
          ((constantSheaf (lisseEtalePrimedTopology f y') AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of (ULift ℤ)))) (add_zero p)).comp
      (Gu.mapExtAddHom
        ((constantSheaf (lisseEtalePrimedTopology f y') AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift ℤ)))
        (lisseEtalePrimedPullback f y' H) p))

/-- Restriction of primed-site cohomology along a morphism of flat-fppf
objects. -/
def flatFppfPrimedCohomologyMap (f : X ⟶ Y) [Flat f]
    {y y' : flatFppfSite Y} (φ : y ⟶ y')
    (H : Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1}) (p : ℕ) :
    ((flatFppfPrimedPullback f y' H).H p) →+
      ((flatFppfPrimedPullback f y H).H p) :=
  let Gu :=
    (CostructuredArrow.map φ).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (flatFppfPrimedTopology f y) (flatFppfPrimedTopology f y')
  ((Ext.mk₀ (flatFppfPrimedConstantPullbackIso f φ).inv).precomp
      (flatFppfPrimedPullback f y H) (zero_add p)).comp
    (((Ext.mk₀ (flatFppfPrimedPullbackMapIso f φ H).hom).postcomp
        (Gu.obj
          ((constantSheaf (flatFppfPrimedTopology f y') AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of (ULift ℤ)))) (add_zero p)).comp
      (Gu.mapExtAddHom
        ((constantSheaf (flatFppfPrimedTopology f y') AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift ℤ)))
        (flatFppfPrimedPullback f y' H) p))

/-- The presheaf sending a lisse-étale object `y` of `Y` to
`H^p((V ×_{y, Y} X)', (pr')⁻¹ H)`. -/
def lisseEtaleHigherDirectImagePresheaf (f : X ⟶ Y) [Smooth f]
    (H : Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1}) (p : ℕ) :
    (lisseEtaleSite Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj y := AddCommGrpCat.of ((lisseEtalePrimedPullback f y.unop H).H p)
  map g := AddCommGrpCat.ofHom (lisseEtalePrimedCohomologyMap f g.unop H p)
  map_id := sorry
  map_comp := sorry

/-- The value of `lisseEtaleHigherDirectImagePresheaf f H p` at `y` is global
cohomology of the primed pullback of `H`. -/
theorem lisseEtaleHigherDirectImagePresheaf_obj (f : X ⟶ Y) [Smooth f]
    (H : Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1}) (p : ℕ)
    (y : lisseEtaleSite Y) :
    (lisseEtaleHigherDirectImagePresheaf f H p).obj (op y) =
      AddCommGrpCat.of ((lisseEtalePrimedPullback f y H).H p) :=
  rfl

/-- The presheaf sending a flat-fppf object `y` of `Y` to
`H^p((V ×_{y, Y} X)', (pr')⁻¹ H)`. -/
def flatFppfHigherDirectImagePresheaf (f : X ⟶ Y) [Flat f]
    (H : Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1}) (p : ℕ) :
    (flatFppfSite Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj y := AddCommGrpCat.of ((flatFppfPrimedPullback f y.unop H).H p)
  map g := AddCommGrpCat.ofHom (flatFppfPrimedCohomologyMap f g.unop H p)
  map_id := sorry
  map_comp := sorry

/-- The value of `flatFppfHigherDirectImagePresheaf f H p` at `y` is global
cohomology of the primed pullback of `H`. -/
theorem flatFppfHigherDirectImagePresheaf_obj (f : X ⟶ Y) [Flat f]
    (H : Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1}) (p : ℕ)
    (y : flatFppfSite Y) :
    (flatFppfHigherDirectImagePresheaf f H p).obj (op y) =
      AddCommGrpCat.of ((flatFppfPrimedPullback f y H).H p) :=
  rfl

end AlgebraicGeometry.AlgebraicStack
