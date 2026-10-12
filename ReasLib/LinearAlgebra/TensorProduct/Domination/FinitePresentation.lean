/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
public import ReasLib.Algebra.Module.FinitePresentation.RingEquiv
public import ReasLib.LinearAlgebra.TensorProduct.BaseRing
public import ReasLib.LinearAlgebra.TensorProduct.Domination
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Detecting tensor-kernel domination on finitely presented modules

Tensor-kernel domination can be tested on finitely presented modules. This filtered-colimit
criterion is kept separate from the elementary domination API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct MonoidalCategory

universe u v w x z

namespace LinearMap

private noncomputable instance preservesColimit_forget_of_filtered
    {S : Type u} [CommRing S]
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ ModuleCat.{max u v} S) :
    PreservesColimit F (forget (ModuleCat.{max u v} S)) :=
  preservesColimit_of_preserves_colimit_cocone
    (ModuleCat.FilteredColimits.colimitCoconeIsColimit F)
    (Types.TypeMax.colimitCoconeIsColimit (F ⋙ forget (ModuleCat.{max u v} S)))

private noncomputable def tensorLeftFunctorEquiv
    {S : Type z} [CommRing S] (L Q : ModuleCat.{z} S) :
    (((MonoidalCategory.tensorLeft L).obj Q : ModuleCat.{z} S) : Type z) ≃ₗ[S]
      (L : Type z) ⊗[S] (Q : Type z) :=
  LinearEquiv.refl S _

private theorem tensorLeftFunctorEquiv_naturality
    {S : Type z} [CommRing S] (L : ModuleCat.{z} S)
    {Q Q' : ModuleCat.{z} S} (f : Q ⟶ Q')
    (a : (((MonoidalCategory.tensorLeft L).obj Q : ModuleCat.{z} S) : Type z)) :
    tensorLeftFunctorEquiv L Q' ((MonoidalCategory.tensorLeft L).map f a) =
      f.hom.lTensor L (tensorLeftFunctorEquiv L Q a) := by
  rfl

private theorem finitePresentation_stage_presentation_sameUniverse
    {S Q : Type z} [CommRing S] [AddCommGroup Q] [Module S Q] :
    ∃ (J : Type z) (_ : SmallCategory J) (_ : IsFiltered J)
      (P : ColimitPresentation J (ModuleCat.of.{z} S Q)),
        ∀ j, Module.FinitePresentation S (P.diag.obj j) := by
  simpa [CategoryTheory.ObjectProperty.ind] using
    (ModuleCat.isFinitePresentation_ind (R := S) (ModuleCat.of.{z} S Q))

private theorem exists_tensor_left_stage_lift_sameUniverse
    {S L J Q : Type z} [CommRing S]
    [AddCommGroup L] [Module S L]
    [SmallCategory J] [IsFiltered J]
    [AddCommGroup Q] [Module S Q]
    (P : ColimitPresentation J (ModuleCat.of.{z} S Q))
    (z : L ⊗[S] Q) :
    ∃ (j : J) (zj : L ⊗[S] P.diag.obj j),
      ((P.ι.app j).hom.lTensor L) zj = z := by
  let Lc := ModuleCat.of.{z} S L
  let c : Cocone (P.diag ⋙ MonoidalCategory.tensorLeft Lc) :=
    (MonoidalCategory.tensorLeft Lc).mapCocone P.cocone
  have hc : IsColimit c :=
    isColimitOfPreserves (MonoidalCategory.tensorLeft Lc) P.isColimit
  let eQ := tensorLeftFunctorEquiv Lc (ModuleCat.of.{z} S Q)
  obtain ⟨j, zjCat, hzjCat⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget (ModuleCat.{z} S)) hc) (eQ.symm z)
  let ej := tensorLeftFunctorEquiv Lc (P.diag.obj j)
  let Qj := ((Functor.const J).obj (ModuleCat.of.{z} S Q)).obj j
  let eQj := tensorLeftFunctorEquiv Lc Qj
  refine ⟨j, ej zjCat, ?_⟩
  have hzjCat' :
      ((MonoidalCategory.tensorLeft Lc).map (P.ι.app j)).hom zjCat = eQ.symm z := by
    change ((MonoidalCategory.tensorLeft Lc).map (P.ι.app j)).hom zjCat =
      eQ.symm z at hzjCat
    exact hzjCat
  calc
    ((P.ι.app j).hom.lTensor L) (ej zjCat) =
        eQj ((MonoidalCategory.tensorLeft Lc).map (P.ι.app j) zjCat) := by
      exact (tensorLeftFunctorEquiv_naturality Lc (P.ι.app j) zjCat).symm
    _ = eQj (eQ.symm z) := congrArg eQj hzjCat'
    _ = z := by rfl

private theorem exists_later_stage_lTensor_eq_zero_sameUniverse
    {S L Q : Type (max u v)} {J : Type v} [CommRing S]
    [AddCommGroup L] [Module S L]
    [SmallCategory J] [IsFiltered J]
    [AddCommGroup Q] [Module S Q]
    (P : ColimitPresentation J (ModuleCat.of.{max u v} S Q))
    {j : J} {z : L ⊗[S] P.diag.obj j}
    (hz : ((P.ι.app j).hom.lTensor L) z = 0) :
    ∃ (j' : J) (e : j ⟶ j'), ((P.diag.map e).hom.lTensor L) z = 0 := by
  let Lc := ModuleCat.of.{max u v} S L
  let c : Cocone (P.diag ⋙ MonoidalCategory.tensorLeft Lc) :=
    (MonoidalCategory.tensorLeft Lc).mapCocone P.cocone
  have hc : IsColimit c :=
    isColimitOfPreserves (MonoidalCategory.tensorLeft Lc) P.isColimit
  let ej := tensorLeftFunctorEquiv Lc (P.diag.obj j)
  let zCat := ej.symm z
  let Qj := ((Functor.const J).obj (ModuleCat.of.{max u v} S Q)).obj j
  let eQj := tensorLeftFunctorEquiv Lc Qj
  have hzCat :
      ((MonoidalCategory.tensorLeft Lc).map (P.ι.app j)).hom zCat = 0 := by
    apply eQj.injective
    calc
      eQj ((MonoidalCategory.tensorLeft Lc).map (P.ι.app j) zCat) =
          (P.ι.app j).hom.lTensor Lc (ej zCat) :=
        tensorLeftFunctorEquiv_naturality Lc (P.ι.app j) zCat
      _ = 0 := by simpa only [ej, zCat, LinearEquiv.apply_symm_apply] using hz
      _ = eQj 0 := by simp
  have hz' :
      ((forget (ModuleCat.{max u v} S)).map (c.ι.app j)) zCat =
        ((forget (ModuleCat.{max u v} S)).map (c.ι.app j)) 0 := by
    change ((MonoidalCategory.tensorLeft Lc).map (P.ι.app j)).hom zCat =
      ((MonoidalCategory.tensorLeft Lc).map (P.ι.app j)).hom 0
    simpa only [map_zero] using hzCat
  obtain ⟨j', e, he⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff'
      (isColimitOfPreserves (forget (ModuleCat.{max u v} S)) hc) zCat 0).1 hz'
  refine ⟨j', e, ?_⟩
  have he' :
      ((MonoidalCategory.tensorLeft Lc).map (P.diag.map e)).hom zCat = 0 := by
    change ((MonoidalCategory.tensorLeft Lc).map (P.diag.map e)).hom zCat =
      ((MonoidalCategory.tensorLeft Lc).map (P.diag.map e)).hom 0 at he
    simpa only [map_zero] using he
  let ej' := tensorLeftFunctorEquiv Lc (P.diag.obj j')
  calc
    ((P.diag.map e).hom.lTensor L) z =
        ((P.diag.map e).hom.lTensor L) (ej zCat) := by
      simp only [zCat, LinearEquiv.apply_symm_apply]
    _ = ej' ((MonoidalCategory.tensorLeft Lc).map (P.diag.map e) zCat) := by
      exact (tensorLeftFunctorEquiv_naturality Lc (P.diag.map e) zCat).symm
    _ = ej' 0 := congrArg ej' he'
    _ = 0 := map_zero ej'

private theorem exists_later_stage_rTensor_eq_zero_sameUniverse
    {S L Q : Type (max u v)} {J : Type v} [CommRing S]
    [AddCommGroup L] [Module S L]
    [SmallCategory J] [IsFiltered J]
    [AddCommGroup Q] [Module S Q]
    (P : ColimitPresentation J (ModuleCat.of.{max u v} S Q))
    {j : J} {a : P.diag.obj j ⊗[S] L}
    (ha : ((P.ι.app j).hom.rTensor L) a = 0) :
    ∃ (j' : J) (e : j ⟶ j'), ((P.diag.map e).hom.rTensor L) a = 0 := by
  let swapj := TensorProduct.comm S (P.diag.obj j) L
  have hcomm_structure :
      (TensorProduct.comm S (ModuleCat.of.{max u v} S Q) L).toLinearMap.comp
          ((P.ι.app j).hom.rTensor L) =
        ((P.ι.app j).hom.lTensor L).comp swapj.toLinearMap := by
    ext q l
    rfl
  have ha_comm :=
    congrArg (TensorProduct.comm S (ModuleCat.of.{max u v} S Q) L) ha
  have ha' : ((P.ι.app j).hom.lTensor L) (swapj a) = 0 := by
    calc
      ((P.ι.app j).hom.lTensor L) (swapj a) =
          (TensorProduct.comm S (ModuleCat.of.{max u v} S Q) L)
            (((P.ι.app j).hom.rTensor L) a) :=
        (LinearMap.congr_fun hcomm_structure a).symm
      _ = (TensorProduct.comm S (ModuleCat.of.{max u v} S Q) L) 0 := ha_comm
      _ = 0 := map_zero _
  obtain ⟨j', e, he⟩ :=
    exists_later_stage_lTensor_eq_zero_sameUniverse (L := L) P ha'
  refine ⟨j', e, ?_⟩
  apply (TensorProduct.comm S (P.diag.obj j') L).injective
  have hcomm_transition :
      (TensorProduct.comm S (P.diag.obj j') L).toLinearMap.comp
          ((P.diag.map e).hom.rTensor L) =
        ((P.diag.map e).hom.lTensor L).comp swapj.toLinearMap := by
    ext q l
    rfl
  calc
    (TensorProduct.comm S (P.diag.obj j') L)
        (((P.diag.map e).hom.rTensor L) a) =
        ((P.diag.map e).hom.lTensor L) (swapj a) :=
      LinearMap.congr_fun hcomm_transition a
    _ = 0 := he
    _ = (TensorProduct.comm S (P.diag.obj j') L) 0 := by simp

set_option maxHeartbeats 600000 in
/-- If a tensor over a stage of a filtered colimit vanishes in the colimit, then it already
vanishes after a later transition map. -/
theorem exists_later_stage_rTensor_eq_zero
    {R : Type u} [CommRing R]
    {J : Type v} {L Q : Type (max u v)}
    [SmallCategory J] [IsFiltered J]
    [AddCommGroup L] [Module R L]
    [AddCommGroup Q] [Module R Q]
    (P : ColimitPresentation J (ModuleCat.of.{max u v} R Q))
    {j : J} {a : P.diag.obj j ⊗[R] L}
    (ha : ((P.ι.app j).hom.rTensor L) a = 0) :
    ∃ (j' : J) (e : j ⟶ j'), ((P.diag.map e).hom.rTensor L) a = 0 := by
  let RU := ULift.{v} R
  let e : R ≃+* RU := ULift.ringEquiv.symm
  let E : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} RU :=
    ModuleCat.restrictScalars e.symm.toRingHom
  let PU : ColimitPresentation J (E.obj (ModuleCat.of.{max u v} R Q)) :=
    { diag := P.diag ⋙ E
      ι := (E.mapCocone P.cocone).ι
      isColimit := isColimitOfPreserves E P.isColimit }
  letI : Module RU L := (E.obj (ModuleCat.of.{max u v} R L)).isModule
  letI : Module RU Q := (E.obj (ModuleCat.of.{max u v} R Q)).isModule
  letI : Module RU (P.diag.obj j) := (PU.diag.obj j).isModule
  let ej := TensorProduct.baseRingSemilinearEquiv e
    (M := P.diag.obj j) (N := L) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
  let eQ := TensorProduct.baseRingSemilinearEquiv e
    (M := Q) (N := L) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
  let aU := ej a
  have hstructure (x : P.diag.obj j ⊗[R] L) :
      ((PU.ι.app j).hom.rTensor L) (ej x) =
        eQ (((P.ι.app j).hom.rTensor L) x) := by
    induction x using TensorProduct.induction_on with
    | zero =>
        calc
          ((PU.ι.app j).hom.rTensor L) (ej 0) =
              ((PU.ι.app j).hom.rTensor L) 0 := congrArg _ (map_zero ej)
          _ = 0 := map_zero _
          _ = eQ 0 := (map_zero eQ).symm
          _ = eQ (((P.ι.app j).hom.rTensor L) 0) :=
            congrArg eQ (map_zero _).symm
    | tmul q l => rfl
    | add x₁ x₂ hx₁ hx₂ =>
        calc
          ((PU.ι.app j).hom.rTensor L) (ej (x₁ + x₂)) =
              ((PU.ι.app j).hom.rTensor L) (ej x₁ + ej x₂) :=
            congrArg _ (map_add ej x₁ x₂)
          _ = ((PU.ι.app j).hom.rTensor L) (ej x₁) +
              ((PU.ι.app j).hom.rTensor L) (ej x₂) := map_add _ _ _
          _ = eQ (((P.ι.app j).hom.rTensor L) x₁) +
              eQ (((P.ι.app j).hom.rTensor L) x₂) := congrArg₂ (· + ·) hx₁ hx₂
          _ = eQ (((P.ι.app j).hom.rTensor L) x₁ +
              ((P.ι.app j).hom.rTensor L) x₂) := (map_add eQ _ _).symm
          _ = eQ (((P.ι.app j).hom.rTensor L) (x₁ + x₂)) :=
            congrArg eQ (map_add _ _ _).symm
  have haU : ((PU.ι.app j).hom.rTensor L) aU = 0 := by
    calc
      ((PU.ι.app j).hom.rTensor L) aU =
          eQ (((P.ι.app j).hom.rTensor L) a) := hstructure a
      _ = eQ 0 := congrArg eQ ha
      _ = 0 := map_zero eQ
  obtain ⟨j', t, ht⟩ :=
    exists_later_stage_rTensor_eq_zero_sameUniverse (L := L) PU haU
  letI : Module RU (P.diag.obj j') := (PU.diag.obj j').isModule
  let ej' := TensorProduct.baseRingSemilinearEquiv e
    (M := P.diag.obj j') (N := L) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
  have htransition (x : P.diag.obj j ⊗[R] L) :
      ej' (((P.diag.map t).hom.rTensor L) x) =
        ((PU.diag.map t).hom.rTensor L) (ej x) := by
    induction x using TensorProduct.induction_on with
    | zero =>
        calc
          ej' (((P.diag.map t).hom.rTensor L) 0) = ej' 0 :=
            congrArg ej' (map_zero _)
          _ = 0 := map_zero ej'
          _ = ((PU.diag.map t).hom.rTensor L) 0 := (map_zero _).symm
          _ = ((PU.diag.map t).hom.rTensor L) (ej 0) :=
            congrArg _ (map_zero ej).symm
    | tmul q l => rfl
    | add x₁ x₂ hx₁ hx₂ =>
        calc
          ej' (((P.diag.map t).hom.rTensor L) (x₁ + x₂)) =
              ej' (((P.diag.map t).hom.rTensor L) x₁ +
                ((P.diag.map t).hom.rTensor L) x₂) :=
            congrArg ej' (map_add _ _ _)
          _ = ej' (((P.diag.map t).hom.rTensor L) x₁) +
              ej' (((P.diag.map t).hom.rTensor L) x₂) := map_add ej' _ _
          _ = ((PU.diag.map t).hom.rTensor L) (ej x₁) +
              ((PU.diag.map t).hom.rTensor L) (ej x₂) := congrArg₂ (· + ·) hx₁ hx₂
          _ = ((PU.diag.map t).hom.rTensor L) (ej x₁ + ej x₂) :=
            (map_add _ _ _).symm
          _ = ((PU.diag.map t).hom.rTensor L) (ej (x₁ + x₂)) :=
            congrArg _ (map_add ej x₁ x₂).symm
  refine ⟨j', t, ?_⟩
  have hzero : ej' (((P.diag.map t).hom.rTensor L) a) = 0 :=
    (htransition a).trans ht
  have hzero' := congrArg ej'.symm hzero
  simpa using hzero'

private theorem dominates_iff_forall_finitePresentation_sameUniverse
    {S A B C : Type z} [CommRing S]
    [AddCommMonoid A] [Module S A]
    [AddCommMonoid B] [Module S B]
    [AddCommMonoid C] [Module S C]
    (g : A →ₗ[S] C) (f : A →ₗ[S] B) :
    g.Dominates f ↔
      ∀ (Q : Type z) [AddCommMonoid Q] [Module S Q]
        [Module.FinitePresentation S Q],
        ker (f.rTensor Q) ≤ ker (g.rTensor Q) := by
  rw [dominates_iff]
  constructor
  · intro h Q _ _ _
    exact h Q
  · intro h Q _ _
    let addA : AddCommMonoid A := inferInstance
    let addB : AddCommMonoid B := inferInstance
    let addC : AddCommMonoid C := inferInstance
    let addQ : AddCommMonoid Q := inferInstance
    letI : AddCommGroup A := Module.addCommMonoidToAddCommGroup S (M := A)
    letI : AddCommGroup B := Module.addCommMonoidToAddCommGroup S (M := B)
    letI : AddCommGroup C := Module.addCommMonoidToAddCommGroup S (M := C)
    letI : AddCommGroup Q := Module.addCommMonoidToAddCommGroup S (M := Q)
    letI : AddCommMonoid A := addA
    letI : AddCommMonoid B := addB
    letI : AddCommMonoid C := addC
    letI : AddCommMonoid Q := addQ
    obtain ⟨J, _, _, P, hP⟩ :=
      finitePresentation_stage_presentation_sameUniverse (S := S) (Q := Q)
    intro y hy
    obtain ⟨j, yj, hyj⟩ :=
      exists_tensor_left_stage_lift_sameUniverse (L := A) P y
    have hfy : (f.rTensor Q) y = 0 := by
      simpa [LinearMap.mem_ker] using hy
    have hf_naturality :
        ((P.ι.app j).hom.lTensor B).comp (f.rTensor (P.diag.obj j)) =
          (f.rTensor Q).comp ((P.ι.app j).hom.lTensor A) := by
      ext a q
      rfl
    have hstage_zero :
        ((P.ι.app j).hom.lTensor B) ((f.rTensor (P.diag.obj j)) yj) = 0 := by
      have happ := LinearMap.congr_fun hf_naturality yj
      change
        ((P.ι.app j).hom.lTensor B) ((f.rTensor (P.diag.obj j)) yj) =
          (f.rTensor Q) (((P.ι.app j).hom.lTensor A) yj) at happ
      calc
        ((P.ι.app j).hom.lTensor B) ((f.rTensor (P.diag.obj j)) yj) =
            (f.rTensor Q) (((P.ι.app j).hom.lTensor A) yj) := happ
        _ = (f.rTensor Q) y := by rw [hyj]
        _ = 0 := hfy
    obtain ⟨j', e, he⟩ :=
      exists_later_stage_lTensor_eq_zero_sameUniverse (L := B) P hstage_zero
    let yj' : A ⊗[S] P.diag.obj j' := ((P.diag.map e).hom.lTensor A) yj
    have hf_transition :
        ((P.diag.map e).hom.lTensor B).comp (f.rTensor (P.diag.obj j)) =
          (f.rTensor (P.diag.obj j')).comp ((P.diag.map e).hom.lTensor A) := by
      ext a q
      rfl
    have hfyj' : (f.rTensor (P.diag.obj j')) yj' = 0 := by
      have happ := LinearMap.congr_fun hf_transition yj
      change
        ((P.diag.map e).hom.lTensor B) ((f.rTensor (P.diag.obj j)) yj) =
          (f.rTensor (P.diag.obj j')) (((P.diag.map e).hom.lTensor A) yj) at happ
      calc
        (f.rTensor (P.diag.obj j')) yj' =
            ((P.diag.map e).hom.lTensor B) ((f.rTensor (P.diag.obj j)) yj) := by
          simpa [yj'] using happ.symm
        _ = 0 := he
    letI : Module.FinitePresentation S (P.diag.obj j') := hP j'
    have hgyj' : (g.rTensor (P.diag.obj j')) yj' = 0 := by
      have hyj'_mem : yj' ∈ ker (f.rTensor (P.diag.obj j')) := by
        simpa [LinearMap.mem_ker] using hfyj'
      simpa [LinearMap.mem_ker] using h (P.diag.obj j') hyj'_mem
    have hleg :
        (P.ι.app j').hom.comp (P.diag.map e).hom = (P.ι.app j).hom := by
      change (P.diag.map e ≫ P.ι.app j').hom = (P.ι.app j).hom
      exact congrArg ModuleCat.Hom.hom (P.w e)
    have htransition (z : A ⊗[S] P.diag.obj j) :
        ((P.ι.app j').hom.lTensor A) (((P.diag.map e).hom.lTensor A) z) =
          ((P.ι.app j).hom.lTensor A) z := by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul a q =>
          change a ⊗ₜ[S] ((P.ι.app j').hom ((P.diag.map e).hom q)) =
            a ⊗ₜ[S] ((P.ι.app j).hom q)
          rw [← LinearMap.comp_apply, hleg]
          rfl
      | add z₁ z₂ hz₁ hz₂ =>
          simp only [map_add]
          rw [hz₁, hz₂]
          rfl
    have hyj'_map : ((P.ι.app j').hom.lTensor A) yj' = y := by
      rw [← hyj]
      exact htransition yj
    have hg_naturality :
        (g.rTensor Q).comp ((P.ι.app j').hom.lTensor A) =
          ((P.ι.app j').hom.lTensor C).comp (g.rTensor (P.diag.obj j')) := by
      ext a q
      rfl
    have hgy : (g.rTensor Q) y = 0 := by
      calc
        (g.rTensor Q) y =
            (g.rTensor Q) (((P.ι.app j').hom.lTensor A) yj') := by rw [hyj'_map]
        _ = ((P.ι.app j').hom.lTensor C) ((g.rTensor (P.diag.obj j')) yj') :=
          LinearMap.congr_fun hg_naturality yj'
        _ = 0 := by rw [hgyj']; simp
    simpa [LinearMap.mem_ker] using hgy

private def overULiftRing
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B]
    (f : A →ₗ[R] B) : A →ₗ[ULift.{z} R] B where
  toFun := f
  map_add' := f.map_add
  map_smul' r a := by
    simpa [ULift.smul_def] using f.map_smul r.down a

private def uliftMap
    {S : Type u} {A : Type v} {B : Type w}
    [CommRing S] [AddCommMonoid A] [Module S A]
    [AddCommMonoid B] [Module S B]
    (f : A →ₗ[S] B) : ULift.{z} A →ₗ[S] ULift.{z} B :=
  ULift.moduleEquiv.symm.toLinearMap.comp
    (f.comp ULift.moduleEquiv.toLinearMap)

private theorem uliftMap_rTensor_apply
    {S : Type u} {A : Type v} {B : Type w}
    [CommRing S] [AddCommMonoid A] [Module S A]
    [AddCommMonoid B] [Module S B]
    (f : A →ₗ[S] B)
    (Q : Type x) [AddCommMonoid Q] [Module S Q]
    (a : ULift.{z} A ⊗[S] Q) :
    ((ULift.moduleEquiv : ULift.{z} B ≃ₗ[S] B).rTensor Q)
        ((uliftMap f).rTensor Q a) =
      (f.rTensor Q)
        (((ULift.moduleEquiv : ULift.{z} A ≃ₗ[S] A).rTensor Q) a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul m q => rfl
  | add a₁ a₂ ha₁ ha₂ => simp only [map_add, ha₁, ha₂]

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]
variable {M' : Type x} [AddCommMonoid M'] [Module R M']

/-- Lemma 10.88.3 (059C): tensor-kernel domination is detected by tensoring with finitely
presented modules. -/
@[stacks 059C]
theorem Dominates.iff_forall_finitePresentation
    (g : M →ₗ[R] M') (f : M →ₗ[R] N) :
    g.Dominates f ↔
      ∀ (Q : Type (max u v w x)) [AddCommMonoid Q] [Module R Q]
        [Module.FinitePresentation R Q],
        ker (f.rTensor Q) ≤ ker (g.rTensor Q) := by
  constructor
  · intro h Q _ _ _
    exact h Q
  · intro h
    let RU := ULift.{max v w x} R
    let e : R ≃+* RU := ULift.ringEquiv.symm
    let fU : M →ₗ[RU] N := overULiftRing f
    let gU : M →ₗ[RU] M' := overULiftRing g
    have hfinite :
        ∀ (Q : Type (max u v w x)) [AddCommMonoid Q] [Module RU Q]
          [Module.FinitePresentation RU Q],
          ker (fU.rTensor Q) ≤ ker (gU.rTensor Q) := by
      intro Q _ _ _
      letI : AddCommGroup Q := Module.addCommMonoidToAddCommGroup RU (M := Q)
      letI : Module R Q := Module.compHom Q e.toRingHom
      letI : Module.FinitePresentation R Q :=
        Module.FinitePresentation.compHom_of_ringEquiv e
      let eM := TensorProduct.baseRingSemilinearEquiv e
        (M := M) (N := Q) (fun _ _ => rfl) (fun _ _ => rfl)
      let eN := TensorProduct.baseRingSemilinearEquiv e
        (M := N) (N := Q) (fun _ _ => rfl) (fun _ _ => rfl)
      let eM' := TensorProduct.baseRingSemilinearEquiv e
        (M := M') (N := Q) (fun _ _ => rfl) (fun _ _ => rfl)
      have hf_base (y : M ⊗[R] Q) :
          eN ((f.rTensor Q) y) = (fU.rTensor Q) (eM y) := by
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul m q => rfl
        | add y₁ y₂ hy₁ hy₂ => simp only [map_add, hy₁, hy₂]
      have hg_base (y : M ⊗[R] Q) :
          eM' ((g.rTensor Q) y) = (gU.rTensor Q) (eM y) := by
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul m q => rfl
        | add y₁ y₂ hy₁ hy₂ => simp only [map_add, hy₁, hy₂]
      intro y hy
      let yR : M ⊗[R] Q := eM.symm y
      have hfyR : (f.rTensor Q) yR = 0 := by
        apply eN.injective
        calc
          eN ((f.rTensor Q) yR) = (fU.rTensor Q) (eM yR) := hf_base yR
          _ = (fU.rTensor Q) y := by rw [eM.apply_symm_apply]
          _ = 0 := LinearMap.mem_ker.mp hy
          _ = eN 0 := by simp
      have hgyR : (g.rTensor Q) yR = 0 :=
        LinearMap.mem_ker.mp (h Q (LinearMap.mem_ker.mpr hfyR))
      apply LinearMap.mem_ker.mpr
      calc
        (gU.rTensor Q) y = (gU.rTensor Q) (eM yR) := by rw [eM.apply_symm_apply]
        _ = eM' ((g.rTensor Q) yR) := (hg_base yR).symm
        _ = 0 := by rw [hgyR]; simp
    let fUU : ULift.{max u v w x} M →ₗ[RU] ULift.{max u v w x} N :=
      uliftMap fU
    let gUU : ULift.{max u v w x} M →ₗ[RU] ULift.{max u v w x} M' :=
      uliftMap gU
    have hfiniteUU :
        ∀ (Q : Type (max u v w x)) [AddCommMonoid Q] [Module RU Q]
          [Module.FinitePresentation RU Q],
          ker (fUU.rTensor Q) ≤ ker (gUU.rTensor Q) := by
      intro Q _ _ _ y hy
      let eM :=
        (ULift.moduleEquiv : ULift.{max u v w x} M ≃ₗ[RU] M).rTensor Q
      let eN :=
        (ULift.moduleEquiv : ULift.{max u v w x} N ≃ₗ[RU] N).rTensor Q
      let eM' :=
        (ULift.moduleEquiv : ULift.{max u v w x} M' ≃ₗ[RU] M').rTensor Q
      have hfy : (fU.rTensor Q) (eM y) = 0 := by
        calc
          (fU.rTensor Q) (eM y) = eN ((fUU.rTensor Q) y) := by
            simpa [fUU, eM, eN] using
              (uliftMap_rTensor_apply fU Q y).symm
          _ = 0 := by rw [LinearMap.mem_ker.mp hy]; simp
      have hgy : (gU.rTensor Q) (eM y) = 0 :=
        LinearMap.mem_ker.mp (hfinite Q (LinearMap.mem_ker.mpr hfy))
      apply LinearMap.mem_ker.mpr
      apply eM'.injective
      calc
        eM' ((gUU.rTensor Q) y) = (gU.rTensor Q) (eM y) := by
          simpa [gUU, eM, eM'] using
            uliftMap_rTensor_apply gU Q y
        _ = 0 := hgy
        _ = eM' 0 := by simp
    have hdomUU :=
      (dominates_iff_forall_finitePresentation_sameUniverse gUU fUU).2 hfiniteUU
    have hU :
        ∀ (Q : Type (max u v w x)) [AddCommMonoid Q] [Module RU Q],
          ker (fU.rTensor Q) ≤ ker (gU.rTensor Q) := by
      intro Q _ _ y hy
      let eM :=
        (ULift.moduleEquiv : ULift.{max u v w x} M ≃ₗ[RU] M).rTensor Q
      let eN :=
        (ULift.moduleEquiv : ULift.{max u v w x} N ≃ₗ[RU] N).rTensor Q
      let eM' :=
        (ULift.moduleEquiv : ULift.{max u v w x} M' ≃ₗ[RU] M').rTensor Q
      let yU := eM.symm y
      have hfyU : (fUU.rTensor Q) yU = 0 := by
        apply eN.injective
        calc
          eN ((fUU.rTensor Q) yU) = (fU.rTensor Q) (eM yU) := by
            simpa [fUU, eM, eN] using
              uliftMap_rTensor_apply fU Q yU
          _ = (fU.rTensor Q) y := by rw [eM.apply_symm_apply]
          _ = 0 := LinearMap.mem_ker.mp hy
          _ = eN 0 := by simp
      have hgyU : (gUU.rTensor Q) yU = 0 :=
        LinearMap.mem_ker.mp (hdomUU Q (LinearMap.mem_ker.mpr hfyU))
      apply LinearMap.mem_ker.mpr
      calc
        (gU.rTensor Q) y = (gU.rTensor Q) (eM yU) := by rw [eM.apply_symm_apply]
        _ = eM' ((gUU.rTensor Q) yU) := by
          simpa [gUU, eM, eM'] using
            (uliftMap_rTensor_apply gU Q yU).symm
        _ = 0 := by rw [hgyU]; simp
    intro Q _ _ y hy
    let eM := TensorProduct.baseRingSemilinearEquiv e
      (M := M) (N := Q) (fun _ _ => rfl) (fun _ _ => rfl)
    let eN := TensorProduct.baseRingSemilinearEquiv e
      (M := N) (N := Q) (fun _ _ => rfl) (fun _ _ => rfl)
    let eM' := TensorProduct.baseRingSemilinearEquiv e
      (M := M') (N := Q) (fun _ _ => rfl) (fun _ _ => rfl)
    have hf_base (a : M ⊗[R] Q) :
        eN ((f.rTensor Q) a) = (fU.rTensor Q) (eM a) := by
      induction a using TensorProduct.induction_on with
      | zero => simp
      | tmul m q => rfl
      | add a₁ a₂ ha₁ ha₂ => simp only [map_add, ha₁, ha₂]
    have hg_base (a : M ⊗[R] Q) :
        eM' ((g.rTensor Q) a) = (gU.rTensor Q) (eM a) := by
      induction a using TensorProduct.induction_on with
      | zero => simp
      | tmul m q => rfl
      | add a₁ a₂ ha₁ ha₂ => simp only [map_add, ha₁, ha₂]
    have hfyU : (fU.rTensor Q) (eM y) = 0 := by
      calc
        (fU.rTensor Q) (eM y) = eN ((f.rTensor Q) y) := (hf_base y).symm
        _ = 0 := by rw [LinearMap.mem_ker.mp hy]; simp
    have hgyU : (gU.rTensor Q) (eM y) = 0 :=
      LinearMap.mem_ker.mp (hU Q (LinearMap.mem_ker.mpr hfyU))
    apply LinearMap.mem_ker.mpr
    apply eM'.injective
    calc
      eM' ((g.rTensor Q) y) = (gU.rTensor Q) (eM y) := hg_base y
      _ = 0 := hgyU
      _ = eM' 0 := by simp

end LinearMap
