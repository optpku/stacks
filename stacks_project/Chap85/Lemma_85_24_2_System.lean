module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.Over.SheafCompose
public import stacks_project.Chap85.Lemma_85_16_3_Component
public import stacks_project.Chap85.Lemma_85_24_2_Cartesian
public import stacks_project.Chap85.Lemma_85_24_2_Component

/-!
# Compatible restrictions of a locally given derived datum along a simplicial SR object

Given a locally given datum `D` and a simplicial object `L` of `SR(B)`, a cartesian object
`E` of `D(O)` on `((C / u(L))_total, O)` is a compatible restriction of `D` when its
two-step restriction to each slice `D(O_{C / u(U_{n,i})})` recovers `E_{U_{n,i}}` via
isomorphisms compatible with the maps `ρ_a`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Sheaf.InternalModule (underlyingApp)
open RingedSite
open RingedSite.Hom
open RingedSite.ModuleDerived
open RingedSite.Localization.AtSimplicialSR
open RingedSite.Localization.AtSimplicialSR.ModuleDerived
open RingedSite.Localization.AtSR
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w uB vB

namespace RingedSite.ModuleDerived.LocallyGiven

open SemiRepresentableFamily
  (OverSite overTopology overSiteDiagram overSiteTotalTopology totalForget overMap
    overIncl overMap_comp_incl forget_comp_incl fiber_comp_totalForget)

variable {X : RingedSite.{u, v, w}}
variable {B : Type uB} [Category.{vB} B]

/-- The simplicial object `K = u(L)` of `SR(C)` obtained by applying `u` componentwise. -/
def simplicialSR (u : B ⥤ X) (L : SimplicialObject (FormalCoproduct.{ι} B)) :
    SimplicialObject (FormalCoproduct.{ι} X.carrier) :=
  L ⋙ SemiRepresentableFamily.map u

/-- The `i`-th object of `K_n = u(L_n)` is `u(U_{n,i})`. -/
theorem simplicialSR_obj (u : B ⥤ X) (L : SimplicialObject (FormalCoproduct.{ι} B))
    (n : SimplexCategory) (i : (L.obj (op n)).I) :
    ((simplicialSR u L).obj (op n)).obj i = u.obj ((L.obj (op n)).obj i) :=
  rfl

/-- Indexing functor of a locally given datum. The `UnivLE.{max u v, w}` argument is
explicit so it cannot be filled by `UnivLE.{max ι u v, w}`. -/
def locallyGivenU (h_le : UnivLE.{max u v, w})
    (D : @LocallyGiven.{u, v, w, w, uB, vB} h_le X B inferInstance) : B ⥤ X :=
  D.u

/-- `locallyGivenU h_le D` is the indexing functor of `D`. -/
theorem locallyGivenU_eq (h_le : UnivLE.{max u v, w})
    (D : @LocallyGiven.{u, v, w, w, uB, vB} h_le X B inferInstance) :
    locallyGivenU h_le D = D.u :=
  sorry

/-- The object `E_U` of a locally given datum. The `UnivLE.{max u v, w}` argument is
explicit so it cannot be filled by `UnivLE.{max ι u v, w}`. -/
def locallyGivenObj (h_le : UnivLE.{max u v, w})
    (D : @LocallyGiven.{u, v, w, w, uB, vB} h_le X B inferInstance) (U : B) :
    Hom.ModuleDerived.{w, max u v, v, w}
      (X.localization ((locallyGivenU h_le D).obj U)) :=
  D.obj U

/-- `locallyGivenObj h_le D U` is the object `E_U` of `D`. -/
theorem locallyGivenObj_eq (h_le : UnivLE.{max u v, w})
    (D : @LocallyGiven.{u, v, w, w, uB, vB} h_le X B inferInstance) (U : B) :
    locallyGivenObj h_le D U =
      D.obj U :=
  sorry

/-- Negative self-Ext vanishing: `Hom(E_U⟦t⟧, E_U) = 0` for every `U` and every `t > 0`. -/
def negativeSelfExt (h_le : UnivLE.{max u v, w})
    (D : @LocallyGiven.{u, v, w, w, uB, vB} h_le X B inferInstance) : Prop :=
  ∀ (U : B) (t : ℤ), 0 < t →
    Subsingleton ((locallyGivenObj h_le D U)⟦t⟧ ⟶ locallyGivenObj h_le D U)

/-- Unfolding of negative self-Ext vanishing. -/
theorem negativeSelfExt_iff (h_le : UnivLE.{max u v, w})
    (D : @LocallyGiven.{u, v, w, w, uB, vB} h_le X B inferInstance) :
    negativeSelfExt h_le D ↔
      ∀ (U : B) (t : ℤ), 0 < t →
        Subsingleton ((locallyGivenObj h_le D U)⟦t⟧ ⟶ locallyGivenObj h_le D U) :=
  sorry

section CarrierUnivLE

variable [h_univLE_carrier : UnivLE.{max u v, w}]

/-- The tautological locally given datum of a global object, with `UnivLE.{max u v, w}` pinned. -/
def globallyGiven (E : Hom.ModuleDerived.{w, u, v, w} X) :
    LocallyGiven.{u, v, w, w, u, v} X X :=
  @ofGlobal.{u, v, w, w} X h_univLE_carrier E

/-- Indexing functor of `globallyGiven E`, with `UnivLE.{max u v, w}` passed explicitly. -/
def globallyGivenU (E : Hom.ModuleDerived.{w, u, v, w} X) : X ⥤ X :=
  locallyGivenU h_univLE_carrier (globallyGiven E)

/-- `globallyGivenU E` is the indexing functor of `globallyGiven E`. -/
theorem globallyGivenU_eq (E : Hom.ModuleDerived.{w, u, v, w} X) :
    globallyGivenU E = locallyGivenU h_univLE_carrier (globallyGiven E) :=
  sorry

end CarrierUnivLE

/-- The simplicial object `K = u(L)` of `SR(C)`, with `UnivLE.{max u v, w}` pinned on `u`. -/
def simplicialK (h_le : UnivLE.{max u v, w})
    (D : @LocallyGiven.{u, v, w, w, uB, vB} h_le X B inferInstance)
    (L : SimplicialObject (FormalCoproduct.{ι} B)) :
    SimplicialObject (FormalCoproduct.{ι} X.carrier) :=
  simplicialSR (locallyGivenU h_le D) L

/-- `simplicialK h_le D L` is `u(L)` with the carrier universe inequality pinned. -/
theorem simplicialK_eq (h_le : UnivLE.{max u v, w})
    (D : @LocallyGiven.{u, v, w, w, uB, vB} h_le X B inferInstance)
    (L : SimplicialObject (FormalCoproduct.{ι} B)) :
    simplicialK h_le D L = simplicialSR (locallyGivenU h_le D) L :=
  sorry

section SliceCore

variable [h_le : UnivLE.{max u v, w}]

/-- Core slice restriction of derived modules, compiled with `UnivLE.{max u v, w}` as an
instance so `restrictionDerived` can be applied directly. -/
def sliceRestrictionDerivedCore {U V : X} (f : V ⟶ U) :
    Hom.ModuleDerived.{w, max u v, v, w} (X.localization U) ⥤
      Hom.ModuleDerived.{w, max u v, v, w} (X.localization V) :=
  restrictionDerived.{u, v, w, w} f

/-- Core exact functor underlying `sliceRestrictionDerivedCore`. -/
def sliceRestrictionExactCore {U V : X} (f : V ⟶ U) :
    ModuleCat.{w} (X.localization U) ⥤ₑ ModuleCat.{w} (X.localization V) :=
  restrictionExact.{u, v, w, w} f


/-- Core ambient restriction to a localization. -/
def sliceLocalizedRestrictionDerivedCore (U : X) :
    Hom.ModuleDerived.{w, u, v, w} X ⥤
      Hom.ModuleDerived.{w, max u v, v, w} (X.localization U) :=
  localizedRestrictionDerived.{w, u, v, w} X U

/-- Core exact functor underlying `sliceLocalizedRestrictionDerivedCore`. -/
def sliceLocalizedRestrictionExactCore (U : X) :
    ModuleCat.{w} X ⥤ₑ ModuleCat.{w} (X.localization U) :=
  localizedRestrictionExact.{u, v, w, w} U

end SliceCore

/-- Slice restriction of derived modules, with `UnivLE.{max u v, w}` passed explicitly. -/
abbrev sliceRestrictionDerived (h_le : UnivLE.{max u v, w}) {U V : X} (f : V ⟶ U) :
    Hom.ModuleDerived.{w, max u v, v, w} (X.localization U) ⥤
      Hom.ModuleDerived.{w, max u v, v, w} (X.localization V) :=
  @sliceRestrictionDerivedCore X h_le _ _ f

/-- The bundled exact functor underlying `sliceRestrictionDerived`. -/
def sliceRestrictionExact (h_le : UnivLE.{max u v, w}) {U V : X} (f : V ⟶ U) :
    ModuleCat.{w} (X.localization U) ⥤ₑ ModuleCat.{w} (X.localization V) :=
  (fun _ : UnivLE.{max u v, w} ↦ sliceRestrictionExactCore f) h_le

/-- Slice restriction of modules along `f : V ⟶ U`, with `UnivLE.{max u v, w}` pinned. -/
def sliceRestriction (h_le : UnivLE.{max u v, w}) {U V : X} (f : V ⟶ U) :
    ModuleCat.{w} (X.localization U) ⥤ ModuleCat.{w} (X.localization V) :=
  (fun _ : UnivLE.{max u v, w} ↦ restriction.{u, v, w, w} f) h_le

/-- `sliceRestriction h_le f` is underived slice restriction. -/
theorem sliceRestriction_eq (h_le : UnivLE.{max u v, w}) {U V : X} (f : V ⟶ U) :
    sliceRestriction h_le f = restriction.{u, v, w, w} f :=
  sorry

/-- Ambient restriction to a localization, with `UnivLE.{max u v, w}` passed explicitly. -/
abbrev sliceLocalizedRestrictionDerived (h_le : UnivLE.{max u v, w}) (U : X) :
    Hom.ModuleDerived.{w, u, v, w} X ⥤
      Hom.ModuleDerived.{w, max u v, v, w} (X.localization U) :=
  @sliceLocalizedRestrictionDerivedCore X h_le U

/-- The bundled exact functor underlying `sliceLocalizedRestrictionDerived`. -/
def sliceLocalizedRestrictionExact (h_le : UnivLE.{max u v, w}) (U : X) :
    ModuleCat.{w} X ⥤ₑ ModuleCat.{w} (X.localization U) :=
  (fun _ : UnivLE.{max u v, w} ↦ sliceLocalizedRestrictionExactCore U) h_le

/-- The transition isomorphism `ρ_a` of a locally given datum, with `UnivLE.{max u v, w}`
pinned so instance search cannot feed `UnivLE.{max ι u v, w}`. -/
def locallyGivenIso (h_le : UnivLE.{max u v, w})
    (D : @LocallyGiven.{u, v, w, w, uB, vB} h_le X B inferInstance)
    {V U : B} (a : V ⟶ U) :
    (sliceRestrictionDerived h_le ((locallyGivenU h_le D).map a)).obj
      (locallyGivenObj h_le D U) ≅ locallyGivenObj h_le D V :=
  D.iso a

/-- `locallyGivenIso h_le D a` is the transition isomorphism `ρ_a` of `D`. -/
theorem locallyGivenIso_eq (h_le : UnivLE.{max u v, w})
    (D : @LocallyGiven.{u, v, w, w, uB, vB} h_le X B inferInstance)
    {V U : B} (a : V ⟶ U) :
    locallyGivenIso h_le D a =
      D.iso a :=
  sorry

variable {h_univLE_carrier : UnivLE.{max u v, w}}

section Data

variable (D : @LocallyGiven.{u, v, w, w, uB, vB} h_univLE_carrier X B inferInstance)
variable (L : SimplicialObject (FormalCoproduct.{ι} B))
variable [h_univLE_index : UnivLE.{max ι u v, w}]
variable [HasSheafify (overSiteTotalTopology X.siteTopology (simplicialK h_univLE_carrier D L)) (Type w)]
variable [HasWeakSheafify (overSiteTotalTopology X.siteTopology (simplicialK h_univLE_carrier D L)) (Type w)]
variable [∀ n : SimplexCategory,
    HasSheafify (overTopology X.siteTopology ((simplicialK h_univLE_carrier D L).obj (op n))) (Type w)]
variable [∀ n : SimplexCategory,
    HasWeakSheafify (overTopology X.siteTopology ((simplicialK h_univLE_carrier D L).obj (op n))) (Type w)]
variable [∀ P : (Grothendieck (overSiteDiagram (simplicialK h_univLE_carrier D L)))ᵒᵖ ⥤ Type w,
    (totalForget (simplicialK h_univLE_carrier D L)).op.HasPointwiseRightKanExtension P]
variable [∀ n : SimplexCategory,
    ∀ P : (OverSite ((simplicialK h_univLE_carrier D L).obj (op n)))ᵒᵖ ⥤ Type w,
      (Grothendieck.ι (overSiteDiagram (simplicialK h_univLE_carrier D L)) (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ∀ P : (OverSite ((simplicialK h_univLE_carrier D L).obj (op n)))ᵒᵖ ⥤ Type w,
      (overMap ((simplicialK h_univLE_carrier D L).map φ.op)).op.HasPointwiseRightKanExtension P]
variable [(overSiteTotalTopology X.siteTopology (simplicialK h_univLE_carrier D L)).HasSheafCompose
    (CategoryTheory.forget RingCat.{w})]
variable [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n : SimplexCategory,
    (overTopology X.siteTopology ((simplicialK h_univLE_carrier D L).obj (op n))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
variable [(SheafOfModules.restrictScalars.{w}
    (toAmbient (simplicialK h_univLE_carrier D L)).structureMap).IsRightAdjoint]
variable [∀ n : SimplexCategory,
    (SheafOfModules.restrictScalars.{w}
      (stageIncl (simplicialK h_univLE_carrier D L) n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (stageMap (simplicialK h_univLE_carrier D L) φ).structureMap).IsRightAdjoint]

/-- Two-step restriction of an object of `D(O)` to the slice `D(O_{C / u(U_{n,i})})`. -/
abbrev stageComponent (n : SimplexCategory) (i : (L.obj (op n)).I) :
    Hom.ModuleDerived.{w} (site (simplicialK h_univLE_carrier D L)) ⥤
      Hom.ModuleDerived.{w} (X.localization (((simplicialK h_univLE_carrier D L).obj (op n)).obj i)) :=
  moduleDerivedComponent (simplicialK h_univLE_carrier D L) n ⋙
    componentDerived ((simplicialK h_univLE_carrier D L).obj (op n)) i

/-- `stageComponent n i` is `Lg_n^*` followed by the `i`-th slice restriction. -/
theorem stageComponent_eq (n : SimplexCategory) (i : (L.obj (op n)).I) :
    stageComponent D L n i =
      moduleDerivedComponent (simplicialK h_univLE_carrier D L) n ⋙
        componentDerived ((simplicialK h_univLE_carrier D L).obj (op n)) i :=
  rfl

/-- Relocalization `overIncl i ⋙ overMap φ` is continuous for the inherited topologies. -/
instance overIncl_comp_overMap_isContinuous {K L : FormalCoproduct.{ι} X.carrier}
    (φ : K ⟶ L) (i : K.I) :
    (overIncl K i ⋙ overMap φ).IsContinuous
      (X.siteTopology.over (K.obj i)) (overTopology X.siteTopology L) :=
  Functor.isContinuous_comp (overIncl K i) (overMap φ)
    (X.siteTopology.over (K.obj i)) (overTopology X.siteTopology K)
    (overTopology X.siteTopology L)

/-- The comparison composite `Over.map (φ.φ i) ⋙ overIncl (φ.f i)` is continuous. -/
instance overMap_slice_comp_overIncl_isContinuous {K L : FormalCoproduct.{ι} X.carrier}
    (φ : K ⟶ L) (i : K.I) :
    (Over.map (φ.φ i) ⋙ overIncl L (φ.f i)).IsContinuous
      (X.siteTopology.over (K.obj i)) (overTopology X.siteTopology L) :=
  Functor.isContinuous_comp (Over.map (φ.φ i)) (overIncl L (φ.f i))
    (X.siteTopology.over (K.obj i)) (X.siteTopology.over (L.obj (φ.f i)))
    (overTopology X.siteTopology L)

/-- Type-valued sheaf comparison of `overIncl i ⋙ overMap φ` with
`Over.map (φ.φ i) ⋙ overIncl (φ.f i)`. -/
def overMapCompIncl_typeIso {K L : FormalCoproduct.{ι} X.carrier}
    (φ : K ⟶ L) (i : K.I) :
    (overIncl K i ⋙ overMap φ).sheafPushforwardContinuous (Type w)
        (X.siteTopology.over (K.obj i)) (overTopology X.siteTopology L) ≅
      (Over.map (φ.φ i) ⋙ overIncl L (φ.f i)).sheafPushforwardContinuous (Type w)
        (X.siteTopology.over (K.obj i)) (overTopology X.siteTopology L) :=
  Functor.sheafPushforwardContinuousIso (overMap_comp_incl φ i) (Type w)
    (X.siteTopology.over (K.obj i)) (overTopology X.siteTopology L)

/-- `overMapCompIncl_typeIso` is continuous pushforward along `overMap_comp_incl`. -/
theorem overMapCompIncl_typeIso_eq {K L : FormalCoproduct.{ι} X.carrier}
    (φ : K ⟶ L) (i : K.I) :
    overMapCompIncl_typeIso φ i =
      Functor.sheafPushforwardContinuousIso (overMap_comp_incl φ i) (Type w)
        (X.siteTopology.over (K.obj i)) (overTopology X.siteTopology L) :=
  sorry

/-- Slice relocalization `Over.map (φ.φ i)` is continuous on inherited over-topologies. -/
instance overMap_component_isContinuous {K L : FormalCoproduct.{ι} X.carrier}
    (φ : K ⟶ L) (i : K.I) :
    (Over.map (φ.φ i)).IsContinuous
      (X.siteTopology.over (K.obj i)) (X.siteTopology.over (L.obj (φ.f i))) :=
  inferInstance

/-- Underlying type-valued sheaf of `component i` compared with continuous pushforward along
`overIncl i`. -/
def component_underlyingApp (K : FormalCoproduct.{ι} X.carrier) (i : K.I)
    (M : SheafOfModules.{w} (ringSheaf K)) :
    (Sheaf.InternalModule.ToInternal.underlying (X.structureSheaf.over (K.obj i))).obj
        ((component K i).obj M) ≅
      ((overIncl K i).sheafPushforwardContinuous (Type w)
          (X.siteTopology.over (K.obj i)) (overTopology X.siteTopology K)).obj
        ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K)).obj M) :=
  (fullyFaithfulSheafToPresheaf (X.siteTopology.over (K.obj i)) (Type w)).preimageIso
    { hom := { app := fun U ↦ 𝟙 _, naturality := fun {_ _} _ ↦ sorry }
      inv := { app := fun U ↦ 𝟙 _, naturality := fun {_ _} _ ↦ sorry }
      hom_inv_id := sorry
      inv_hom_id := sorry }

/-- Underlying type-valued sheaf of slice restriction along an arrow of `X`. -/
def sliceRestriction_underlyingApp {U V : X} (f : V ⟶ U)
    (M : SheafOfModules.{w} (X.structureSheaf.over U)) :
    (Sheaf.InternalModule.ToInternal.underlying (X.structureSheaf.over V)).obj
        ((sliceRestriction h_univLE_carrier f).obj M) ≅
      ((Over.map f).sheafPushforwardContinuous (Type w)
          (X.siteTopology.over V) (X.siteTopology.over U)).obj
        ((Sheaf.InternalModule.ToInternal.underlying (X.structureSheaf.over U)).obj M) :=
  (fullyFaithfulSheafToPresheaf (X.siteTopology.over V) (Type w)).preimageIso
    { hom := { app := fun W ↦ 𝟙 _, naturality := fun {_ _} _ ↦ sorry }
      inv := { app := fun W ↦ 𝟙 _, naturality := fun {_ _} _ ↦ sorry }
      hom_inv_id := sorry
      inv_hom_id := sorry }

/-- Continuous-pushforward composition of `overIncl i` with `overMap` of `K.map φ.op`. -/
def componentStageMap_inclMapComp {m n : SimplexCategory} (φ : m ⟶ n)
    (i : (L.obj (op n)).I) :
    (overMap ((simplicialK h_univLE_carrier D L).map φ.op)).sheafPushforwardContinuous (Type w)
        (overTopology X.siteTopology ((simplicialK h_univLE_carrier D L).obj (op n)))
        (overTopology X.siteTopology ((simplicialK h_univLE_carrier D L).obj (op m))) ⋙
      (overIncl ((simplicialK h_univLE_carrier D L).obj (op n)) i).sheafPushforwardContinuous
        (Type w)
        (X.siteTopology.over (((simplicialK h_univLE_carrier D L).obj (op n)).obj i))
        (overTopology X.siteTopology ((simplicialK h_univLE_carrier D L).obj (op n))) ≅
      (overIncl ((simplicialK h_univLE_carrier D L).obj (op n)) i ⋙
          overMap ((simplicialK h_univLE_carrier D L).map φ.op)).sheafPushforwardContinuous
        (Type w)
        (X.siteTopology.over (((simplicialK h_univLE_carrier D L).obj (op n)).obj i))
        (overTopology X.siteTopology ((simplicialK h_univLE_carrier D L).obj (op m))) :=
  NatIso.ofComponents
    (fun F ↦
      (fullyFaithfulSheafToPresheaf
          (X.siteTopology.over (((simplicialK h_univLE_carrier D L).obj (op n)).obj i))
          (Type w)).preimageIso
        { hom := { app := fun U ↦ 𝟙 _, naturality := fun {_ _} _ ↦ sorry }
          inv := { app := fun U ↦ 𝟙 _, naturality := fun {_ _} _ ↦ sorry }
          hom_inv_id := sorry
          inv_hom_id := sorry })
    sorry

/-- Inverse of `componentStageMap_inclMapComp` is the reverse composition comparison. -/
theorem componentStageMap_inclMapComp_hom_inv_id {m n : SimplexCategory} (φ : m ⟶ n)
    (i : (L.obj (op n)).I) :
    (componentStageMap_inclMapComp D L φ i).hom ≫
      (componentStageMap_inclMapComp D L φ i).inv = 𝟙 _ :=
  sorry

/-- Continuous-pushforward composition of `Over.map (φ.φ i)` with `overIncl (φ.f i)`. -/
def componentStageMap_mapInclComp {m n : SimplexCategory} (φ : m ⟶ n)
    (i : (L.obj (op n)).I) :
    (overIncl ((simplicialK h_univLE_carrier D L).obj (op m))
          (((simplicialK h_univLE_carrier D L).map φ.op).f i)).sheafPushforwardContinuous
        (Type w)
        (X.siteTopology.over
          (((simplicialK h_univLE_carrier D L).obj (op m)).obj
            (((simplicialK h_univLE_carrier D L).map φ.op).f i)))
        (overTopology X.siteTopology ((simplicialK h_univLE_carrier D L).obj (op m))) ⋙
      (Over.map (((simplicialK h_univLE_carrier D L).map φ.op).φ i)).sheafPushforwardContinuous
        (Type w)
        (X.siteTopology.over (((simplicialK h_univLE_carrier D L).obj (op n)).obj i))
        (X.siteTopology.over
          (((simplicialK h_univLE_carrier D L).obj (op m)).obj
            (((simplicialK h_univLE_carrier D L).map φ.op).f i))) ≅
      (Over.map (((simplicialK h_univLE_carrier D L).map φ.op).φ i) ⋙
          overIncl ((simplicialK h_univLE_carrier D L).obj (op m))
            (((simplicialK h_univLE_carrier D L).map φ.op).f i)).sheafPushforwardContinuous
        (Type w)
        (X.siteTopology.over (((simplicialK h_univLE_carrier D L).obj (op n)).obj i))
        (overTopology X.siteTopology ((simplicialK h_univLE_carrier D L).obj (op m))) :=
  NatIso.ofComponents
    (fun F ↦
      (fullyFaithfulSheafToPresheaf
          (X.siteTopology.over (((simplicialK h_univLE_carrier D L).obj (op n)).obj i))
          (Type w)).preimageIso
        { hom := { app := fun U ↦ 𝟙 _, naturality := fun {_ _} _ ↦ sorry }
          inv := { app := fun U ↦ 𝟙 _, naturality := fun {_ _} _ ↦ sorry }
          hom_inv_id := sorry
          inv_hom_id := sorry })
    sorry

/-- Inverse of `componentStageMap_mapInclComp` is the reverse composition comparison. -/
theorem componentStageMap_mapInclComp_hom_inv_id {m n : SimplexCategory} (φ : m ⟶ n)
    (i : (L.obj (op n)).I) :
    (componentStageMap_mapInclComp D L φ i).hom ≫
      (componentStageMap_mapInclComp D L φ i).inv = 𝟙 _ :=
  sorry

/-- Objectwise underlying comparison of the two restriction paths along a simplex operator. -/
def componentStageMap_underlyingApp {m n : SimplexCategory} (φ : m ⟶ n)
    (i : (L.obj (op n)).I)
    (M : SheafOfModules.{w}
      (ringSheaf ((simplicialK h_univLE_carrier D L).obj (op m)))) :
    (Sheaf.InternalModule.ToInternal.underlying
        (X.structureSheaf.over
          (((simplicialK h_univLE_carrier D L).obj (op n)).obj i))).obj
      ((component ((simplicialK h_univLE_carrier D L).obj (op n)) i).obj
        ((stageMap (simplicialK h_univLE_carrier D L) φ).modulePullback.obj M)) ≅
      (Sheaf.InternalModule.ToInternal.underlying
          (X.structureSheaf.over
            (((simplicialK h_univLE_carrier D L).obj (op n)).obj i))).obj
        ((sliceRestriction h_univLE_carrier
            (((simplicialK h_univLE_carrier D L).map φ.op).φ i)).obj
          ((component ((simplicialK h_univLE_carrier D L).obj (op m))
              ((L.map φ.op).f i)).obj M)) :=
  component_underlyingApp (h_univLE_carrier := h_univLE_carrier)
      ((simplicialK h_univLE_carrier D L).obj (op n)) i
      ((stageMap (simplicialK h_univLE_carrier D L) φ).modulePullback.obj M) ≪≫
    ((overIncl ((simplicialK h_univLE_carrier D L).obj (op n)) i).sheafPushforwardContinuous
        (Type w)
        (X.siteTopology.over (((simplicialK h_univLE_carrier D L).obj (op n)).obj i))
        (overTopology X.siteTopology ((simplicialK h_univLE_carrier D L).obj (op n)))).mapIso
      (stageMap_modulePullback_underlyingIso (simplicialK h_univLE_carrier D L) φ M) ≪≫
    (componentStageMap_inclMapComp D L φ i).app
      ((Sheaf.InternalModule.ToInternal.underlying
          (ringSheaf ((simplicialK h_univLE_carrier D L).obj (op m)))).obj M) ≪≫
    (overMapCompIncl_typeIso ((simplicialK h_univLE_carrier D L).map φ.op) i).app
      ((Sheaf.InternalModule.ToInternal.underlying
          (ringSheaf ((simplicialK h_univLE_carrier D L).obj (op m)))).obj M) ≪≫
    (componentStageMap_mapInclComp D L φ i).symm.app
      ((Sheaf.InternalModule.ToInternal.underlying
          (ringSheaf ((simplicialK h_univLE_carrier D L).obj (op m)))).obj M) ≪≫
    ((Over.map (((simplicialK h_univLE_carrier D L).map φ.op).φ i)).sheafPushforwardContinuous
        (Type w)
        (X.siteTopology.over (((simplicialK h_univLE_carrier D L).obj (op n)).obj i))
        (X.siteTopology.over
          (((simplicialK h_univLE_carrier D L).obj (op m)).obj
            (((simplicialK h_univLE_carrier D L).map φ.op).f i)))).mapIso
      (component_underlyingApp (h_univLE_carrier := h_univLE_carrier)
        ((simplicialK h_univLE_carrier D L).obj (op m))
        (((simplicialK h_univLE_carrier D L).map φ.op).f i) M).symm ≪≫
    (sliceRestriction_underlyingApp (h_univLE_carrier := h_univLE_carrier)
      (((simplicialK h_univLE_carrier D L).map φ.op).φ i)
      ((component ((simplicialK h_univLE_carrier D L).obj (op m))
          ((L.map φ.op).f i)).obj M)).symm

/-- `componentStageMap_underlyingApp` is the objectwise underlying comparison of the two
restriction paths. -/
theorem componentStageMap_underlyingApp_hom_inv_id {m n : SimplexCategory} (φ : m ⟶ n)
    (i : (L.obj (op n)).I)
    (M : SheafOfModules.{w}
      (ringSheaf ((simplicialK h_univLE_carrier D L).obj (op m)))) :
    (componentStageMap_underlyingApp D L φ i M).hom ≫
      (componentStageMap_underlyingApp D L φ i M).inv = 𝟙 _ :=
  sorry

/-- The specified component comparison is natural in the input module sheaf. -/
theorem componentStageMap_underlyingApp_naturality {m n : SimplexCategory} (φ : m ⟶ n)
    (i : (L.obj (op n)).I)
    {M N : SheafOfModules.{w}
      (ringSheaf ((simplicialK h_univLE_carrier D L).obj (op m)))} (f : M ⟶ N) :
    ((stageMap (simplicialK h_univLE_carrier D L) φ).modulePullback ⋙
          component ((simplicialK h_univLE_carrier D L).obj (op n)) i ⋙
            Sheaf.InternalModule.ToInternal.underlying
              (X.structureSheaf.over
                (((simplicialK h_univLE_carrier D L).obj (op n)).obj i))).map f ≫
        (componentStageMap_underlyingApp D L φ i N).hom =
      (componentStageMap_underlyingApp D L φ i M).hom ≫
        (component ((simplicialK h_univLE_carrier D L).obj (op m)) ((L.map φ.op).f i) ⋙
          sliceRestriction h_univLE_carrier
            (((simplicialK h_univLE_carrier D L).map φ.op).φ i) ⋙
            Sheaf.InternalModule.ToInternal.underlying
              (X.structureSheaf.over
                (((simplicialK h_univLE_carrier D L).obj (op n)).obj i))).map f :=
  sorry

/-- Underlying type-valued sheaf functor comparison of the two restriction paths. -/
def componentStageMap_underlyingNatIso {m n : SimplexCategory} (φ : m ⟶ n)
    (i : (L.obj (op n)).I) :
    (stageMap (simplicialK h_univLE_carrier D L) φ).modulePullback ⋙
        component ((simplicialK h_univLE_carrier D L).obj (op n)) i ⋙
          Sheaf.InternalModule.ToInternal.underlying
            (X.structureSheaf.over
              (((simplicialK h_univLE_carrier D L).obj (op n)).obj i)) ≅
      component ((simplicialK h_univLE_carrier D L).obj (op m)) ((L.map φ.op).f i) ⋙
        sliceRestriction h_univLE_carrier
          (((simplicialK h_univLE_carrier D L).map φ.op).φ i) ⋙
          Sheaf.InternalModule.ToInternal.underlying
            (X.structureSheaf.over
              (((simplicialK h_univLE_carrier D L).obj (op n)).obj i)) :=
  NatIso.ofComponents (fun M ↦ componentStageMap_underlyingApp D L φ i M)
    (componentStageMap_underlyingApp_naturality D L φ i)

/-- `componentStageMap_underlyingNatIso` is the functorial form of
`componentStageMap_underlyingApp`. -/
theorem componentStageMap_underlyingNatIso_eq {m n : SimplexCategory} (φ : m ⟶ n)
    (i : (L.obj (op n)).I) :
    componentStageMap_underlyingNatIso D L φ i =
      NatIso.ofComponents (fun M ↦ componentStageMap_underlyingApp D L φ i M)
        (componentStageMap_underlyingApp_naturality D L φ i) :=
  sorry

/-- The specified canonical comparison preserves addition in its target module structure. -/
theorem componentStageMap_underlyingNatIso_add {m n : SimplexCategory} (φ : m ⟶ n)
    (i : (L.obj (op n)).I)
    (M : SheafOfModules.{w}
      (ringSheaf ((simplicialK h_univLE_carrier D L).obj (op m))))
    (U : (Over (((simplicialK h_univLE_carrier D L).obj (op n)).obj i))ᵒᵖ)
    (x y : ((component ((simplicialK h_univLE_carrier D L).obj (op n)) i).obj
        ((stageMap (simplicialK h_univLE_carrier D L) φ).modulePullback.obj M)).val.obj U) :
    underlyingApp (X.structureSheaf.over
        (((simplicialK h_univLE_carrier D L).obj (op n)).obj i))
        ((componentStageMap_underlyingNatIso D L φ i).hom.app M) U (x + y) =
      underlyingApp (X.structureSheaf.over
        (((simplicialK h_univLE_carrier D L).obj (op n)).obj i))
        ((componentStageMap_underlyingNatIso D L φ i).hom.app M) U x +
        underlyingApp (X.structureSheaf.over
          (((simplicialK h_univLE_carrier D L).obj (op n)).obj i))
          ((componentStageMap_underlyingNatIso D L φ i).hom.app M) U y :=
  sorry

/-- The specified canonical comparison preserves the target ring's scalar action. -/
theorem componentStageMap_underlyingNatIso_smul {m n : SimplexCategory} (φ : m ⟶ n)
    (i : (L.obj (op n)).I)
    (M : SheafOfModules.{w}
      (ringSheaf ((simplicialK h_univLE_carrier D L).obj (op m))))
    (U : (Over (((simplicialK h_univLE_carrier D L).obj (op n)).obj i))ᵒᵖ)
    (r : (X.structureSheaf.over
        (((simplicialK h_univLE_carrier D L).obj (op n)).obj i)).obj.obj U)
    (x : ((component ((simplicialK h_univLE_carrier D L).obj (op n)) i).obj
        ((stageMap (simplicialK h_univLE_carrier D L) φ).modulePullback.obj M)).val.obj U) :
    underlyingApp (X.structureSheaf.over
        (((simplicialK h_univLE_carrier D L).obj (op n)).obj i))
        ((componentStageMap_underlyingNatIso D L φ i).hom.app M) U (r • x) =
      r • underlyingApp (X.structureSheaf.over
        (((simplicialK h_univLE_carrier D L).obj (op n)).obj i))
        ((componentStageMap_underlyingNatIso D L φ i).hom.app M) U x :=
  sorry

/-- Underived identification of slice restriction after `f_φ^*` with slice restriction along
`φ.φ i` after the `φ.f i`-th component. -/
def componentStageMapIso {m n : SimplexCategory} (φ : m ⟶ n)
    (i : (L.obj (op n)).I) :
    (stageMap (simplicialK h_univLE_carrier D L) φ).modulePullback ⋙
        component ((simplicialK h_univLE_carrier D L).obj (op n)) i ≅
      component ((simplicialK h_univLE_carrier D L).obj (op m)) ((L.map φ.op).f i) ⋙
        sliceRestriction h_univLE_carrier
          (((simplicialK h_univLE_carrier D L).map φ.op).φ i) :=
  Sheaf.InternalModule.functorIsoOfUnderlying
    (X.structureSheaf.over
      (((simplicialK h_univLE_carrier D L).obj (op n)).obj i))
    (componentStageMap_underlyingNatIso D L φ i)
    (componentStageMap_underlyingNatIso_add D L φ i)
    (componentStageMap_underlyingNatIso_smul D L φ i)

/-- `componentStageMapIso` is the module-level lift of `componentStageMap_underlyingNatIso`. -/
theorem componentStageMapIso_eq {m n : SimplexCategory} (φ : m ⟶ n)
    (i : (L.obj (op n)).I) :
    componentStageMapIso D L φ i =
      Sheaf.InternalModule.functorIsoOfUnderlying
        (X.structureSheaf.over
          (((simplicialK h_univLE_carrier D L).obj (op n)).obj i))
        (componentStageMap_underlyingNatIso D L φ i)
        (componentStageMap_underlyingNatIso_add D L φ i)
        (componentStageMap_underlyingNatIso_smul D L φ i) :=
  sorry

/-- Derived identification of `(componentDerived i).obj (L(f_φ)^* E_m)` with the iterated
slice restriction of `E_m` along `u((L.map φ.op).φ i)`. -/
def componentDerivedStageMapIso {m n : SimplexCategory} (φ : m ⟶ n)
    (i : (L.obj (op n)).I)
    (E : Hom.ModuleDerived.{w} (site (simplicialK h_univLE_carrier D L))) :
    (componentDerived ((simplicialK h_univLE_carrier D L).obj (op n)) i).obj
        ((stageMapExact (simplicialK h_univLE_carrier D L) φ).mapDerivedCategory.obj
          ((moduleDerivedComponent (simplicialK h_univLE_carrier D L) m).obj E)) ≅
      (sliceRestrictionDerived h_univLE_carrier
          ((locallyGivenU h_univLE_carrier D).map ((L.map φ.op).φ i))).obj
        ((stageComponent D L m ((L.map φ.op).f i)).obj E) :=
  ((ExactFunctor.MapDerivedCategory.compFunctorIso
        (stageMapExact (simplicialK h_univLE_carrier D L) φ)
        (componentExact ((simplicialK h_univLE_carrier D L).obj (op n)) i)).symm.app
      ((moduleDerivedComponent (simplicialK h_univLE_carrier D L) m).obj E)) ≪≫
    ((ExactFunctor.MapDerivedCategory.mapIso
        (ObjectProperty.isoMk (exactFunctor _ _) (componentStageMapIso D L φ i))).app
      ((moduleDerivedComponent (simplicialK h_univLE_carrier D L) m).obj E)) ≪≫
    ((ExactFunctor.MapDerivedCategory.compFunctorIso
        (componentExact ((simplicialK h_univLE_carrier D L).obj (op m))
          ((L.map φ.op).f i))
        (sliceRestrictionExact h_univLE_carrier
          ((locallyGivenU h_univLE_carrier D).map ((L.map φ.op).φ i)))).app
      ((moduleDerivedComponent (simplicialK h_univLE_carrier D L) m).obj E))

/-- `componentDerivedStageMapIso` is the derived functor of `componentStageMapIso` after
composition comparisons. -/
theorem componentDerivedStageMapIso_eq {m n : SimplexCategory} (φ : m ⟶ n)
    (i : (L.obj (op n)).I)
    (E : Hom.ModuleDerived.{w} (site (simplicialK h_univLE_carrier D L))) :
    componentDerivedStageMapIso D L φ i E =
      ((ExactFunctor.MapDerivedCategory.compFunctorIso
            (stageMapExact (simplicialK h_univLE_carrier D L) φ)
            (componentExact ((simplicialK h_univLE_carrier D L).obj (op n)) i)).symm.app
          ((moduleDerivedComponent (simplicialK h_univLE_carrier D L) m).obj E)) ≪≫
        ((ExactFunctor.MapDerivedCategory.mapIso
            (ObjectProperty.isoMk (exactFunctor _ _)
              (componentStageMapIso D L φ i))).app
          ((moduleDerivedComponent (simplicialK h_univLE_carrier D L) m).obj E)) ≪≫
        ((ExactFunctor.MapDerivedCategory.compFunctorIso
            (componentExact ((simplicialK h_univLE_carrier D L).obj (op m))
              ((L.map φ.op).f i))
            (sliceRestrictionExact h_univLE_carrier
              ((locallyGivenU h_univLE_carrier D).map ((L.map φ.op).φ i)))).app
          ((moduleDerivedComponent (simplicialK h_univLE_carrier D L) m).obj E)) :=
  sorry

/-- A compatible restriction of a locally given derived datum along a simplicial object of
`SR(B)` is a family of isomorphisms identifying the two-step restriction of `E` with
`E_{U_{n,i}}`, compatible with the maps `ρ_a`. -/
structure CompatibleRestriction (E : Hom.ModuleDerived.{w} (site (simplicialK h_univLE_carrier D L))) where
  /-- The restriction of `E` to `D(O_{C / u(U_{n,i})})` is `E_{U_{n,i}}`. -/
  iso : ∀ (n : SimplexCategory) (i : (L.obj (op n)).I),
    (stageComponent D L n i).obj E ≅ locallyGivenObj h_univLE_carrier D ((L.obj (op n)).obj i)
  /-- Compatibility with `ρ_a` along `L.map φ.op`: after the named comparison
  `componentDerivedStageMapIso`, the slice identifications intertwine `ρ_a`. -/
  iso_comp : ∀ {m n : SimplexCategory} (φ : m ⟶ n) (i : (L.obj (op n)).I),
    (componentDerived ((simplicialK h_univLE_carrier D L).obj (op n)) i).map
          (moduleDerivedTransition (simplicialK h_univLE_carrier D L) φ E) ≫
        (iso n i).hom =
      (componentDerivedStageMapIso D L φ i E).hom ≫
        (sliceRestrictionDerived h_univLE_carrier
            ((locallyGivenU h_univLE_carrier D).map ((L.map φ.op).φ i))).map
            (iso m ((L.map φ.op).f i)).hom ≫
          (locallyGivenIso h_univLE_carrier D ((L.map φ.op).φ i)).hom

/-- The restriction isomorphisms of a compatible restriction. -/
def CompatibleRestriction.iso_apply {E : Hom.ModuleDerived.{w} (site (simplicialK h_univLE_carrier D L))}
    (h : CompatibleRestriction D L E)
    (n : SimplexCategory) (i : (L.obj (op n)).I) :
    (stageComponent D L n i).obj E ≅ locallyGivenObj h_univLE_carrier D ((L.obj (op n)).obj i) :=
  h.iso n i

/-- Source-semantic readout of a compatible restriction: the slice restriction isos together
with the `ρ_a` cocycle. -/
theorem CompatibleRestriction.spec {E : Hom.ModuleDerived.{w} (site (simplicialK h_univLE_carrier D L))}
    (h : CompatibleRestriction D L E)
    {m n : SimplexCategory} (φ : m ⟶ n) (i : (L.obj (op n)).I) :
    (componentDerived ((simplicialK h_univLE_carrier D L).obj (op n)) i).map
          (moduleDerivedTransition (simplicialK h_univLE_carrier D L) φ E) ≫
        (h.iso n i).hom =
      (componentDerivedStageMapIso D L φ i E).hom ≫
        (sliceRestrictionDerived h_univLE_carrier
            ((locallyGivenU h_univLE_carrier D).map ((L.map φ.op).φ i))).map
            (h.iso m ((L.map φ.op).f i)).hom ≫
          (locallyGivenIso h_univLE_carrier D ((L.map φ.op).φ i)).hom :=
  sorry

/-- An isomorphism of cartesian objects is compatible with two compatible restrictions when
its two-step restrictions intertwine the slice identifications. -/
abbrev CompatibleRestriction.IsCompatibleIso
    {E E' : Hom.ModuleDerived.{w} (site (simplicialK h_univLE_carrier D L))}
    (hE : CompatibleRestriction D L E) (hE' : CompatibleRestriction D L E')
    (e : E ≅ E') : Prop :=
  ∀ (n : SimplexCategory) (i : (L.obj (op n)).I),
    (stageComponent D L n i).map e.hom ≫ (hE'.iso n i).hom = (hE.iso n i).hom

/-- Equational form of compatibility of an isomorphism between compatible restrictions. -/
theorem CompatibleRestriction.IsCompatibleIso.w
    {E E' : Hom.ModuleDerived.{w} (site (simplicialK h_univLE_carrier D L))}
    {hE : CompatibleRestriction D L E} {hE' : CompatibleRestriction D L E'} {e : E ≅ E'}
    (h : CompatibleRestriction.IsCompatibleIso D L hE hE' e)
    (n : SimplexCategory) (i : (L.obj (op n)).I) :
    (stageComponent D L n i).map e.hom ≫ (hE'.iso n i).hom = (hE.iso n i).hom :=
  sorry

/-- Underived functor identifying `a^*` then `g_n^*` then the `i`-th slice with ambient
restriction to `C / K_{n,i}`. -/
def toSliceFunctorIso (n : SimplexCategory) (i : (L.obj (op n)).I) :
    ((toAmbient (simplicialK h_univLE_carrier D L)).modulePullback ⋙
        (stageIncl (simplicialK h_univLE_carrier D L) n).modulePullback) ⋙
          component.{ι, u, v, w, w} ((simplicialK h_univLE_carrier D L).obj (op n)) i ≅
      localizedRestriction.{w} X (((simplicialK h_univLE_carrier D L).obj (op n)).obj i) :=
  Functor.isoWhiskerRight
      (toAmbient_comp_stageInclIso (simplicialK h_univLE_carrier D L) n)
      (component.{ι, u, v, w, w} ((simplicialK h_univLE_carrier D L).obj (op n)) i) ≪≫
    sliceInverseImageNatIso ((simplicialK h_univLE_carrier D L).obj (op n)) i ≪≫
    (localizedRestrictionIsoInverseImage
      (((simplicialK h_univLE_carrier D L).obj (op n)).obj i)).symm

/-- Exact-functor form of `toSliceFunctorIso`. -/
def toSliceExactIso (n : SimplexCategory) (i : (L.obj (op n)).I) :
    ((toAmbientExact (simplicialK h_univLE_carrier D L)).comp
          (stageInclExact (simplicialK h_univLE_carrier D L) n)).comp
        (componentExact ((simplicialK h_univLE_carrier D L).obj (op n)) i) ≅
      sliceLocalizedRestrictionExact h_univLE_carrier (((simplicialK h_univLE_carrier D L).obj (op n)).obj i) :=
  ObjectProperty.isoMk (exactFunctor _ _) (toSliceFunctorIso D L n i)

/-- Derived identification of `La^*` then `Lg_n^*` then the `i`-th slice with
`j[U_{n,i}]⁻¹`. -/
def toSliceDerivedIso (n : SimplexCategory) (i : (L.obj (op n)).I) :
    toAmbientDerived (simplicialK h_univLE_carrier D L) ⋙ stageComponent D L n i ≅
      sliceLocalizedRestrictionDerived h_univLE_carrier (((simplicialK h_univLE_carrier D L).obj (op n)).obj i) :=
  ((Functor.associator (toAmbientDerived (simplicialK h_univLE_carrier D L))
          (moduleDerivedComponent (simplicialK h_univLE_carrier D L) n)
          (componentDerived ((simplicialK h_univLE_carrier D L).obj (op n)) i)).symm ≪≫
      Functor.isoWhiskerRight
        (ExactFunctor.MapDerivedCategory.compFunctorIso
          (toAmbientExact (simplicialK h_univLE_carrier D L)) (stageInclExact (simplicialK h_univLE_carrier D L) n)).symm
        (componentDerived ((simplicialK h_univLE_carrier D L).obj (op n)) i)) ≪≫
    (ExactFunctor.MapDerivedCategory.compFunctorIso
        ((toAmbientExact (simplicialK h_univLE_carrier D L)).comp (stageInclExact (simplicialK h_univLE_carrier D L) n))
        (componentExact ((simplicialK h_univLE_carrier D L).obj (op n)) i)).symm ≪≫
    ExactFunctor.MapDerivedCategory.mapIso (toSliceExactIso D L n i)

/-- `toSliceDerivedIso` is the derived functor of `toSliceFunctorIso` after composition
comparisons. -/
theorem toSliceDerivedIso_eq (n : SimplexCategory) (i : (L.obj (op n)).I) :
    toSliceDerivedIso D L n i =
      ((Functor.associator (toAmbientDerived (simplicialK h_univLE_carrier D L))
            (moduleDerivedComponent (simplicialK h_univLE_carrier D L) n)
            (componentDerived ((simplicialK h_univLE_carrier D L).obj (op n)) i)).symm ≪≫
        Functor.isoWhiskerRight
          (ExactFunctor.MapDerivedCategory.compFunctorIso
            (toAmbientExact (simplicialK h_univLE_carrier D L)) (stageInclExact (simplicialK h_univLE_carrier D L) n)).symm
          (componentDerived ((simplicialK h_univLE_carrier D L).obj (op n)) i)) ≪≫
      (ExactFunctor.MapDerivedCategory.compFunctorIso
          ((toAmbientExact (simplicialK h_univLE_carrier D L)).comp (stageInclExact (simplicialK h_univLE_carrier D L) n))
          (componentExact ((simplicialK h_univLE_carrier D L).obj (op n)) i)).symm ≪≫
      ExactFunctor.MapDerivedCategory.mapIso (toSliceExactIso D L n i) :=
  sorry

end Data

section OfGlobal

variable (E : Hom.ModuleDerived.{w, u, v, w} X)
variable (L : SimplicialObject (FormalCoproduct.{ι} X))

/-- The simplicial object `K = u(L)` for the tautological locally given datum of `E`. -/
abbrev globallyGivenK : SimplicialObject (FormalCoproduct.{ι} X.carrier) :=
  simplicialK h_univLE_carrier (@globallyGiven X h_univLE_carrier E) L

/-- `globallyGivenK E L` is `simplicialK` of `globallyGiven E`. -/
theorem globallyGivenK_eq :
    globallyGivenK E L =
      simplicialK h_univLE_carrier (@globallyGiven X h_univLE_carrier E) L :=
  sorry

variable [h_univLE_index : UnivLE.{max ι u v, w}]
variable [HasSheafify (overSiteTotalTopology X.siteTopology (globallyGivenK E L))
    (Type w)]
variable [HasWeakSheafify (overSiteTotalTopology X.siteTopology (globallyGivenK E L))
    (Type w)]
variable [∀ n : SimplexCategory,
    HasSheafify (overTopology X.siteTopology ((globallyGivenK E L).obj (op n)))
      (Type w)]
variable [∀ n : SimplexCategory,
    HasWeakSheafify (overTopology X.siteTopology ((globallyGivenK E L).obj (op n)))
      (Type w)]
variable [∀ P : (Grothendieck (overSiteDiagram (globallyGivenK E L)))ᵒᵖ ⥤ Type w,
    (totalForget (globallyGivenK E L)).op.HasPointwiseRightKanExtension P]
variable [∀ n : SimplexCategory,
    ∀ P : (OverSite ((globallyGivenK E L).obj (op n)))ᵒᵖ ⥤ Type w,
      (Grothendieck.ι (overSiteDiagram (globallyGivenK E L))
        (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ∀ P : (OverSite ((globallyGivenK E L).obj (op n)))ᵒᵖ ⥤ Type w,
      (overMap ((globallyGivenK E L).map φ.op)).op.HasPointwiseRightKanExtension P]
variable [(overSiteTotalTopology X.siteTopology (globallyGivenK E L)).HasSheafCompose
    (CategoryTheory.forget RingCat.{w})]
variable [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n : SimplexCategory,
    (overTopology X.siteTopology ((globallyGivenK E L).obj (op n))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
variable [(SheafOfModules.restrictScalars.{w}
    (toAmbient (globallyGivenK E L)).structureMap).IsRightAdjoint]
variable [∀ n : SimplexCategory,
    (SheafOfModules.restrictScalars.{w}
      (stageIncl (globallyGivenK E L) n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (stageMap (globallyGivenK E L) φ).structureMap).IsRightAdjoint]

/-- The tautological compatible restriction of `globallyGiven E` along a simplicial object of
`SR(C)`, obtained by pulling `E` back along `a`. -/
def CompatibleRestriction.ofGlobal :
    CompatibleRestriction (@globallyGiven X h_univLE_carrier E) L
      ((toAmbientDerived (globallyGivenK E L)).obj E) where
  iso n i := (toSliceDerivedIso (@globallyGiven X h_univLE_carrier E) L n i).app E
  iso_comp := sorry

/-- The tautological compatible restriction of `globallyGiven E` uses `toSliceDerivedIso`. -/
theorem CompatibleRestriction.ofGlobal_iso (n : SimplexCategory) (i : (L.obj (op n)).I) :
    ((CompatibleRestriction.ofGlobal E L).iso n i).hom =
      (toSliceDerivedIso (@globallyGiven X h_univLE_carrier E) L n i).hom.app E :=
  sorry

end OfGlobal

end RingedSite.ModuleDerived.LocallyGiven
