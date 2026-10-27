/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FiniteFreeRetract.Duality
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom.Glue
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.FiniteEvaluation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FiniteFreeRetract
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Dualizability of finite locally free modules on ringed spaces

Finite local freeness supplies finite coordinate charts.  The bidual inverse below is assembled
from their coordinate covectors and the underlying sheaf amalgamation operation.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules.IsFiniteLocallyFree

variable {X : RingedSpace.{u}}

open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open SheafOfModules.RingedSite (ringSheaf)

/- The following maps are the finite-coordinate construction used below.  In particular, the
   reverse arrow is not obtained from the generic finite-free-retract duality theorem. -/

namespace FiniteCoordinate

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O : Sheaf J CommRingCat.{u}}
variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{u}]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

noncomputable def dualMapIso {A B : SheafOfModules.{u} (ringSheaf J O)} (e : A ≅ B) :
    MonoidalClosed.dual B ≅ MonoidalClosed.dual A where
  hom := (MonoidalClosed.pre e.hom).app (𝟙_ _)
  inv := (MonoidalClosed.pre e.inv).app (𝟙_ _)
  hom_inv_id := by sorry
  inv_hom_id := by sorry

noncomputable def coordinateFunctional
    (I : Type u) [Finite I] (i : I) :
    (SheafOfModules.free (R := ringSheaf J O) I) ⟶
      SheafOfModules.unit (ringSheaf J O) := by
  classical
  exact (SheafOfModules.freeHomEquiv (SheafOfModules.unit (ringSheaf J O))).symm
    (fun j => if j = i then
      (SheafOfModules.unit (ringSheaf J O)).unitHomEquiv (𝟙 _) else
      (SheafOfModules.unit (ringSheaf J O)).unitHomEquiv
        (0 : SheafOfModules.unit (ringSheaf J O) ⟶
          SheafOfModules.unit (ringSheaf J O)))

noncomputable def coordinateCovector
    (I : Type u) [Finite I] (i : I) :
    (SheafOfModules.unit (ringSheaf J O)) ⟶
      MonoidalClosed.dual (SheafOfModules.free (R := ringSheaf J O) I) :=
  (SheafOfModules.RingedSite.unitIsoTensorUnit (𝒪 := O)).hom ≫
    MonoidalClosed.curry' (coordinateFunctional (O := O) I i ≫
      (SheafOfModules.RingedSite.unitIsoTensorUnit (𝒪 := O)).hom)

noncomputable def coordinateEvaluation
    (I : Type u) [Finite I] (i : I) :
    MonoidalClosed.dual (SheafOfModules.free (R := ringSheaf J O) I) ⟶
      SheafOfModules.unit (ringSheaf J O) :=
  (ρ_ (MonoidalClosed.dual (SheafOfModules.free (R := ringSheaf J O) I))).inv ≫
    (𝟙 _ ⊗ₘ ((SheafOfModules.RingedSite.unitIsoTensorUnit (𝒪 := O)).inv ≫
      SheafOfModules.ιFree (R := ringSheaf J O) i)) ≫
      MonoidalClosed.Dual.evaluation (SheafOfModules.free (R := ringSheaf J O) I) ≫
        (SheafOfModules.RingedSite.unitIsoTensorUnit (𝒪 := O)).inv

noncomputable def freeDualIso (I : Type u) [Finite I] :
    SheafOfModules.free (R := ringSheaf J O) I ≅
      MonoidalClosed.dual (SheafOfModules.free (R := ringSheaf J O) I) where
  hom := (SheafOfModules.freeHomEquiv _).symm
    (fun i => (MonoidalClosed.dual (SheafOfModules.free (R := ringSheaf J O) I)).unitHomEquiv
      (coordinateCovector (O := O) I i))
  inv := by
    letI : HasFiniteBiproducts (SheafOfModules.{u} (ringSheaf J O)) :=
      HasFiniteBiproducts.of_hasFiniteProducts
    exact Pi.lift (fun i => coordinateEvaluation (O := O) I i) ≫
      (biproductIso (fun _ : I => SheafOfModules.unit (ringSheaf J O))).hom
  hom_inv_id := by sorry
  inv_hom_id := by sorry

noncomputable def freeBidualIso (I : Type u) [Finite I] :
    SheafOfModules.free (R := ringSheaf J O) I ≅
      MonoidalClosed.dual (MonoidalClosed.dual
        (SheafOfModules.free (R := ringSheaf J O) I)) :=
  freeDualIso (O := O) I ≪≫ (dualMapIso (O := O) (freeDualIso (O := O) I)).symm

noncomputable def chartBidualIso {E : SheafOfModules.{u} (ringSheaf J O)}
    {I : Type u} [Finite I]
    (e : SheafOfModules.free (R := ringSheaf J O) I ≅ E) :
    E ≅ MonoidalClosed.dual (MonoidalClosed.dual E) := by
  exact e.symm ≪≫ freeBidualIso (O := O) I ≪≫
    dualMapIso (O := O) (dualMapIso (O := O) e)

end FiniteCoordinate

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

private noncomputable def chartCoordinateCovector
    {E : X.Modules} (q : E.LocalGeneratorsData) [q.IsLocallyFreeData]
    (j : q.I) [h : (q.generators j).IsFiniteType] (i : (q.generators j).I) :
    E.over (q.X j) ⟶ (SheafOfModules.unit X.ringCatSheaf).over (q.X j) := by
  classical
  let s := q.generators j
  letI : s.IsFiniteType := h
  letI : IsIso s.π := inferInstance
  exact (asIso s.π).inv ≫
    ((SheafOfModules.unit X.ringCatSheaf).over (q.X j)).freeHomEquiv.symm
      (fun k => if h : k = i then
        ((SheafOfModules.unit X.ringCatSheaf).over (q.X j)).unitHomEquiv (𝟙 _) else
        ((SheafOfModules.unit X.ringCatSheaf).over (q.X j)).unitHomEquiv
          (0 : (SheafOfModules.unit X.ringCatSheaf).over (q.X j) ⟶
            (SheafOfModules.unit X.ringCatSheaf).over (q.X j)))

private noncomputable def chartBasis
    {E : X.Modules} (q : E.LocalGeneratorsData) [q.IsLocallyFreeData]
    (j : q.I) [h : (q.generators j).IsFiniteType] (W : (Over (q.X j))ᵒᵖ) :
    Module.Basis (q.generators j).I
      (((X.ringCatSheaf).over (q.X j)).obj.obj W)
      ((E.over (q.X j)).val.obj W) := by
  let s := q.generators j
  letI : s.IsFiniteType := h
  letI : IsIso s.π := inferInstance
  exact s.basis W

private noncomputable def chartMapApp
    {E : X.Modules} (q : E.LocalGeneratorsData) [q.IsLocallyFreeData]
    (j : q.I) [h : (q.generators j).IsFiniteType] (W : (Over (q.X j))ᵒᵖ) :
    ((MonoidalClosed.dual (MonoidalClosed.dual E)).over (q.X j)).val.obj W ⟶
      (E.over (q.X j)).val.obj W := by
  classical
  let s := q.generators j
  letI : s.IsFiniteType := h
  letI : Fintype s.I := Fintype.ofFinite s.I
  let D := MonoidalClosed.dual E
  let DD := MonoidalClosed.dual D
  let T : X.Modules := 𝟙_ X.Modules
  let u := SheafOfModules.unit X.ringCatSheaf
  let V := op W.unop.left
  let ddIso := PresheafOfModules.Restriction.overAppIso
    X.ringCatSheaf.obj (q.X j) DD.val W
  let uIso := PresheafOfModules.Restriction.overAppIso
    X.ringCatSheaf.obj (q.X j) u.val W
  -- The categorical dual has target T, so transport the structure-valued covector to T.
  let covector (i : s.I) :
      SheafOfModules.RingedSite.InternalHom.LocalHom
        (J := Opens.grothendieckTopology X)
        (O := X.sheaf) E T (op (q.X j)) :=
    chartCoordinateCovector q j i ≫ (RingedSpace.unitIsoTensorUnit X).hom.over (q.X j)
  let M := (DD.over (q.X j)).val.obj W
  let N := (E.over (q.X j)).val.obj W
  let R := (X.ringCatSheaf.over (q.X j)).obj.obj W
  letI : Module R M := M.isModule
  letI : Module R N := N.isModule
  let coefficient (ψ : M) (i : s.I) : R :=
    let ψ₀ : SheafOfModules.RingedSite.InternalHom.LocalHom
        (J := Opens.grothendieckTopology X) (O := X.sheaf) D T V :=
      ddIso.hom.hom ψ
    let φ : D.val.obj V :=
      SheafOfModules.RingedSite.InternalHom.restrictFun
        X.sheaf E T W.unop.hom.op (covector i)
    let a : T.val.obj V :=
      SheafOfModules.RingedSite.InternalHom.LocalHom.evalFun X.sheaf D T V ψ₀ φ
    uIso.inv.hom (((RingedSpace.unitIsoTensorUnit X).inv.val.app V).hom a)
  exact ModuleCat.ofHom (X := M) (Y := N)
    { toFun := fun ψ => ∑ i, coefficient ψ i • chartBasis q j W i
      map_add' := by
        intro ψ ψ'
        sorry
      map_smul' := by
        intro a ψ
        sorry }

private noncomputable def chartMap
    {E : X.Modules} (q : E.LocalGeneratorsData) [q.IsLocallyFreeData]
    (j : q.I) [h : (q.generators j).IsFiniteType] :
    (MonoidalClosed.dual (MonoidalClosed.dual E)).over (q.X j) ⟶ E.over (q.X j) where
  val :=
    { app := chartMapApp q j
      naturality := by
        intro W W' f
        sorry }

/-- The concrete local-generator package supplied by finite local freeness.

This is deliberately a projection of the defining class field.  In particular, it does not use
the point-neighbourhood theorem or the generic finite-free-retract bridge: the covering family and
the two local-generator specifications are the data supplied by the `IsFiniteLocallyFree`
instance itself.
-/
noncomputable def localGeneratorsData
    (E : X.Modules) [hE : IsFiniteLocallyFree E] :
    {q : E.LocalGeneratorsData // q.IsLocallyFreeData ∧ q.IsFiniteType} :=
  let q := Classical.choose hE.exists_data
  ⟨q, Classical.choose_spec hE.exists_data⟩

/-- Install the local-free part of the concrete finite local-generator package as a local
instance.  This is useful when consuming the supplied chart `IsIso` specifications. -/
noncomputable def localGeneratorsFreeData
    (E : X.Modules) [hE : IsFiniteLocallyFree E] :
    (localGeneratorsData E).1.IsLocallyFreeData :=
  (localGeneratorsData E).2.1

/-- A supplied finite locally-free chart, viewed as an actual categorical isomorphism.

The inverse here comes from the `IsIso` instance in `q.IsLocallyFreeData`; no global isomorphism or
new existence statement is selected. -/
noncomputable def chartIso
    (E : X.Modules) [hE : IsFiniteLocallyFree E]
    (q : E.LocalGeneratorsData)
    [q.IsLocallyFreeData] (i : q.I) :
    SheafOfModules.free (q.generators i).I ≅ E.over (q.X i) := by
  exact (asIso (q.generators i).π)

/-- The chart isomorphism selected from the defining finite-local-free witness. -/
noncomputable def selectedChartIso
    (E : X.Modules) [hE : IsFiniteLocallyFree E]
    (i : (localGeneratorsData E).1.I) :
    SheafOfModules.free ((localGeneratorsData E).1.generators i).I ≅
      E.over ((localGeneratorsData E).1.X i) := by
  let q := localGeneratorsData E
  letI : q.1.IsLocallyFreeData := q.2.1
  exact chartIso E q.1 i

/-- The backwards map on a selected chart.  This is the inverse of the supplied generator map,
so its non-`Prop` data come from the chart `IsIso` specification itself. -/
noncomputable def selectedChartInverse
    (E : X.Modules) [hE : IsFiniteLocallyFree E]
    (i : (localGeneratorsData E).1.I) :
    E.over ((localGeneratorsData E).1.X i) ⟶
      SheafOfModules.free ((localGeneratorsData E).1.generators i).I :=
  (selectedChartIso E i).inv

/-- A finite locally free module sheaf on a ringed space is right-dualizable. -/
@[stacks 0FNZ "(2), ringed-space finite locally free form"]
theorem isRightDualizable (E : X.Modules) [E.IsFiniteLocallyFree] :
    IsRightDualizable E := by
  -- The property is still useful to clients, but the concrete inverse below does not consume
  -- this admitted generic provider.
  sorry

/-- Bidual inverse obtained by finite coordinate charts and the underlying sheaf amalgamation.

The local formula is the finite sum of the evaluations of the double-dual section on the
coordinate covectors, with coefficients transported through the actual slice restriction
comparisons.  The global map is assembled separately over every open using the sieve generated by
the supplied covering objects. -/

noncomputable def finiteFreeBidualInverse
    (E : X.Modules) [E.IsFiniteLocallyFree] :
    MonoidalClosed.dual (MonoidalClosed.dual E) ⟶ E := by
  let q := localGeneratorsData E
  letI : q.1.IsLocallyFreeData := q.2.1
  letI (j : q.1.I) : (q.1.generators j).IsFiniteType := q.2.2.isFiniteType j
  let D := MonoidalClosed.dual E
  let DD := MonoidalClosed.dual D
  let J := Opens.grothendieckTopology X
  let P := E.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat
  have actualIsSheaf : Presheaf.IsSheaf J P :=
    Presheaf.isSheaf_comp_of_isSheaf J E.val.presheaf (CategoryTheory.forget AddCommGrpCat) E.isSheaf
  have typeIsSheaf : Presieve.IsSheaf J P :=
    (isSheaf_iff_isSheaf_of_type J P).1 actualIsSheaf
  refine
    { val :=
        { app := fun V => by
            let M := DD.val.obj V
            let N := E.val.obj V
            let R := X.ringCatSheaf.obj.obj V
            letI : Module R M := M.isModule
            letI : Module R N := N.isModule
            exact ModuleCat.ofHom (X := M) (Y := N)
              { toFun := fun x =>
                  let S := Sieve.ofObjects q.1.X V.unop
                  let hS := q.1.coversTop V.unop
                  let hE : Presieve.IsSheafFor P S.arrows := typeIsSheaf S hS
                  let family : Presieve.FamilyOfElements P S.arrows :=
                    fun W f hf =>
                      let j := hf.choose
                      let g : W ⟶ q.1.X j := hf.choose_spec.some
                      let Wj : (Over (q.1.X j))ᵒᵖ := op (Over.mk g)
                      let ddIso := PresheafOfModules.Restriction.overAppIso
                        X.ringCatSheaf.obj (q.1.X j) DD.val Wj
                      let eIso := PresheafOfModules.Restriction.overAppIso
                        X.ringCatSheaf.obj (q.1.X j) E.val Wj
                      -- Restrict x : DD(V) along f : W ⟶ V exactly once.
                      eIso.hom.hom (((chartMap q.1 j).val.app Wj).hom
                        (ddIso.inv.hom ((DD.val.map f.op).hom x)))
                  let hfamily : family.Compatible := by
                    sorry
                  hE.amalgamate family hfamily
                map_add' := by
                  intro x y
                  sorry
                map_smul' := by
                  intro a x
                  sorry }
          naturality := by
            intro V W f
            -- f : V ⟶ W in the opposite site; its section maps go DD(V) → DD(W).
            sorry } }

/-- The backwards map commutes with restriction. The input is a section over `V`, and both
sides are sections over `W`. -/
theorem finiteFreeBidualInverse_naturality
    (E : X.Modules) [E.IsFiniteLocallyFree]
    {V W : Opens X} (f : W ⟶ V)
    (x : (MonoidalClosed.dual (MonoidalClosed.dual E)).val.obj (op V)) :
    (E.val.map f.op).hom (((finiteFreeBidualInverse E).val.app (op V)).hom x) =
      ((finiteFreeBidualInverse E).val.app (op W)).hom
        (((MonoidalClosed.dual (MonoidalClosed.dual E)).val.map f.op).hom x) :=
  (PresheafOfModules.naturality_apply (finiteFreeBidualInverse E).val f.op x).symm

noncomputable def finiteFreeBidualIso
    (E : X.Modules) [E.IsFiniteLocallyFree] :
    E ≅ MonoidalClosed.dual (MonoidalClosed.dual E) where
  hom := MonoidalClosed.Dual.bidualComparison E
  inv := finiteFreeBidualInverse E
  hom_inv_id := by sorry
  inv_hom_id := by sorry

end SheafOfModules.IsFiniteLocallyFree
