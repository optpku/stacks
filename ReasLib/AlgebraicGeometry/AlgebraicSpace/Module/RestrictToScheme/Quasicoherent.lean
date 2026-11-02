/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.ExtensionBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.ExtensionMonoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Tensor

/-!
# The specified comparisons on quasi-coherent modules

The counit and pullback comparisons below are maps of the actual geometric
adjunctions. Invertibility is asserted only on quasi-coherent inputs.
-/

@[expose] public section
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.RelativeProj
open SheafOfModules.RingedSite
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme
variable {S : Scheme.{u}} {T Z : Over S}

/-- Sectionwise preimages of the canonical comparison, with zero fallback, define its inverse. -/
def counitInverse (Z : Over S) (M : (ofOver Z).Modules) [M.IsQuasicoherent] :
    M ⟶ (extension Z).obj ((Modules.restrictToScheme Z).obj M) := by
  let A := (extension Z).obj ((Modules.restrictToScheme Z).obj M)
  let B := M
  let f : A ⟶ B := (extensionAdjunction Z).counit.app M
  let inv := fun (V : (smallEtaleSite (ofOver Z))ᵒᵖ) ↦ preimageOr 0 (fun x ↦ (f.val.app V).hom x)
  have laws :
      (∀ V (x y : B.val.obj V), inv V (x + y) = inv V x + inv V y) ∧
      (∀ V (r : (structureSheaf (ofOver Z)).obj.obj V) (x : B.val.obj V), inv V (r • x) = r • inv V x) ∧
      (∀ {V W : (smallEtaleSite (ofOver Z))ᵒᵖ} (i : V ⟶ W) (x : B.val.obj V),
        A.val.map i (inv V x) = inv W (B.val.map i x)) := by sorry
  exact { val := {
    app := fun V ↦ @ModuleCat.ofHom ((structureSheaf (ofOver Z)).obj.obj V) _
      (B.val.obj V) (A.val.obj V)
      (B.val.obj V).isAddCommGroup (B.val.obj V).isModule
      (A.val.obj V).isAddCommGroup (A.val.obj V).isModule {
      toFun := inv V
      map_add' := laws.1 V
      map_smul' := laws.2.1 V }
    naturality := by
      intro V W i
      ext x
      exact (laws.2.2 i x).symm } }

/-- The canonical comparison and its specified inverse give an isomorphism on quasi-coherent inputs. -/
def counitIso (Z : Over S) (M : (ofOver Z).Modules) [M.IsQuasicoherent] : (extension Z).obj ((Modules.restrictToScheme Z).obj M) ≅ M := by
  let hom : (extension Z).obj ((Modules.restrictToScheme Z).obj M) ⟶ M := (extensionAdjunction Z).counit.app M
  let inv : M ⟶ (extension Z).obj ((Modules.restrictToScheme Z).obj M) := counitInverse Z M
  have laws : hom ≫ inv = 𝟙 _ ∧ inv ≫ hom = 𝟙 _ := by sorry
  exact ⟨hom, inv, laws.1, laws.2⟩

/-- The extension counit is invertible on quasi-coherent modules. -/
instance counit_isIso (Z : Over S) (M : (ofOver Z).Modules) [M.IsQuasicoherent] : IsIso ((extensionAdjunction Z).counit.app M) :=
  (counitIso Z M).isIso_hom

/-- Sectionwise preimages of the canonical comparison, with zero fallback, define its inverse. -/
def unitInverse (Z : Over S) (M : Z.left.Modules) [M.IsQuasicoherent] :
    (Modules.restrictToScheme Z).obj ((extension Z).obj M) ⟶ M := by
  let A := M
  let B := (Modules.restrictToScheme Z).obj ((extension Z).obj M)
  let f : A ⟶ B := (extensionAdjunction Z).unit.app M
  let inv := fun (V : Z.left.Opensᵒᵖ) ↦ preimageOr 0 (fun x ↦ (f.val.app V).hom x)
  have laws :
      (∀ V (x y : B.val.obj V), inv V (x + y) = inv V x + inv V y) ∧
      (∀ V (r : Z.left.ringCatSheaf.obj.obj V) (x : B.val.obj V), inv V (r • x) = r • inv V x) ∧
      (∀ {V W : Z.left.Opensᵒᵖ} (i : V ⟶ W) (x : B.val.obj V),
        A.val.map i (inv V x) = inv W (B.val.map i x)) := by sorry
  exact { val := {
    app := fun V ↦ @ModuleCat.ofHom (Z.left.ringCatSheaf.obj.obj V) _
      (B.val.obj V) (A.val.obj V)
      (B.val.obj V).isAddCommGroup (B.val.obj V).isModule
      (A.val.obj V).isAddCommGroup (A.val.obj V).isModule {
      toFun := inv V
      map_add' := laws.1 V
      map_smul' := laws.2.1 V }
    naturality := by
      intro V W i
      ext x
      exact (laws.2.2 i x).symm } }

/-- The canonical comparison and its specified inverse give an isomorphism on quasi-coherent inputs. -/
def unitIso (Z : Over S) (M : Z.left.Modules) [M.IsQuasicoherent] : M ≅ (Modules.restrictToScheme Z).obj ((extension Z).obj M) := by
  let hom : M ⟶ (Modules.restrictToScheme Z).obj ((extension Z).obj M) := (extensionAdjunction Z).unit.app M
  let inv : (Modules.restrictToScheme Z).obj ((extension Z).obj M) ⟶ M := unitInverse Z M
  have laws : hom ≫ inv = 𝟙 _ ∧ inv ≫ hom = 𝟙 _ := by sorry
  exact ⟨hom, inv, laws.1, laws.2⟩

/-- The extension unit is invertible on quasi-coherent scheme modules. -/
instance unit_isIso (Z : Over S) (M : Z.left.Modules) [M.IsQuasicoherent] : IsIso ((extensionAdjunction Z).unit.app M) :=
  (unitIso Z M).isIso_hom

/-- Extension of the Zariski pullback maps to the etale pullback by the counit. -/
def extensionPullbackComparison (t : T ⟶ Z) (M : (ofOver Z).Modules) :
    (extension T).obj ((Scheme.Modules.pullback t.left).obj
      ((Modules.restrictToScheme Z).obj M)) ⟶ (Modules.pullback (ofOverMap t)).obj M :=
  (extensionPullbackIso t).hom.app ((Modules.restrictToScheme Z).obj M) ≫
    (Modules.pullback (ofOverMap t)).map ((extensionAdjunction Z).counit.app M)

/-- The extension-pullback comparison is invertible on quasi-coherent modules. -/
instance extensionPullbackComparison_isIso (t : T ⟶ Z) (M : (ofOver Z).Modules)
    [M.IsQuasicoherent] : IsIso (extensionPullbackComparison t M) :=
  ((extensionPullbackIso t).app ((Modules.restrictToScheme Z).obj M) ≪≫
    (Modules.pullback (ofOverMap t)).mapIso (counitIso Z M)).isIso_hom

/-- On QCoh this adjoint map is invertible, without an etale hypothesis on `t`. -/
instance pullbackComparison_isIso (t : T ⟶ Z) (M : (ofOver Z).Modules)
    [M.IsQuasicoherent] : IsIso (pullbackComparison t M) :=
  (restrictPullbackIso t M).isIso_inv

/-- QCoh tensor powers restrict by the actual lax unit/tensor maps. -/
def tensorPowerComparison (Z : Over S) (L : (ofOver Z).Modules) (n : ℕ) :
    RingedSpace.TensorPower.sheaf ((Modules.restrictToScheme Z).obj L) n ⟶
      (Modules.restrictToScheme Z).obj (tensorPowerUnit L n) :=
  Nat.rec (unitMap Z)
    (fun k rec ↦ (𝟙 _ ⊗ₘ rec) ≫ Modules.restrictTensorLax L (tensorPowerUnit L k)) n

/-- The recursive tensor-power comparison is bijective on sections of quasi-coherent inputs. -/
theorem tensorPowerComparison_bijective (Z : Over S) (L : (ofOver Z).Modules)
    [L.IsQuasicoherent] (n : ℕ) (V : Z.left.Opensᵒᵖ) :
    Function.Bijective ((tensorPowerComparison Z L n).val.app V).hom := by
  have hqc : ∀ k, (tensorPowerUnit L k).IsQuasicoherent := by
    intro k
    induction k with
    | zero =>
        change (SheafOfModules.unit (structureSheaf (ofOver Z))).IsQuasicoherent
        infer_instance
    | succ k ih =>
        letI := ih
        change (L ⊗ tensorPowerUnit L k).IsQuasicoherent
        infer_instance
  have hiso : ∀ k, IsIso (tensorPowerComparison Z L k) := by
    intro k
    induction k with
    | zero =>
        change IsIso (unitMap Z)
        infer_instance
    | succ k ih =>
        letI := ih
        letI := hqc k
        change IsIso ((𝟙 _ ⊗ₘ tensorPowerComparison Z L k) ≫
          Modules.restrictTensorLax L (tensorPowerUnit L k))
        exact ((Iso.refl _ ⊗ᵢ asIso (tensorPowerComparison Z L k)) ≪≫
          Modules.restrictTensorIso L (tensorPowerUnit L k)).isIso_hom
  letI := hiso n
  exact ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.evaluation Z.left.ringCatSheaf V).map (tensorPowerComparison Z L n))

/-- Sectionwise preimages of the canonical comparison, with zero fallback, define its inverse. -/
def tensorPowerInverse (Z : Over S) (L : (ofOver Z).Modules) [L.IsQuasicoherent] (n : ℕ) :
    (Modules.restrictToScheme Z).obj (tensorPowerUnit L n) ⟶ RingedSpace.TensorPower.sheaf ((Modules.restrictToScheme Z).obj L) n := by
  let A := RingedSpace.TensorPower.sheaf ((Modules.restrictToScheme Z).obj L) n
  let B := (Modules.restrictToScheme Z).obj (tensorPowerUnit L n)
  let f : A ⟶ B := tensorPowerComparison Z L n
  let inv := fun (V : Z.left.Opensᵒᵖ) ↦ preimageOr 0 (fun x ↦ (f.val.app V).hom x)
  have laws :
      (∀ V (x y : B.val.obj V), inv V (x + y) = inv V x + inv V y) ∧
      (∀ V (r : Z.left.ringCatSheaf.obj.obj V) (x : B.val.obj V), inv V (r • x) = r • inv V x) ∧
      (∀ {V W : Z.left.Opensᵒᵖ} (i : V ⟶ W) (x : B.val.obj V),
        A.val.map i (inv V x) = inv W (B.val.map i x)) := by
    have hbij (V : Z.left.Opensᵒᵖ) : Function.Bijective (fun x ↦ (f.val.app V).hom x) :=
      tensorPowerComparison_bijective Z L n V
    have hright (V : Z.left.Opensᵒᵖ) :
        Function.RightInverse (inv V) (fun x ↦ (f.val.app V).hom x) :=
      preimageOr_rightInverse 0 _ (hbij V).2
    refine ⟨?_, ?_, ?_⟩
    · intro V x y
      apply (hbij V).1
      calc
        (f.val.app V).hom (inv V (x + y)) = x + y := hright V _
        _ = (f.val.app V).hom (inv V x) + (f.val.app V).hom (inv V y) :=
          (congrArg₂ (· + ·) (hright V x) (hright V y)).symm
        _ = (f.val.app V).hom (inv V x + inv V y) :=
          ((f.val.app V).hom.map_add _ _).symm
    · intro V r x
      apply (hbij V).1
      calc
        (f.val.app V).hom (inv V (r • x)) = r • x := hright V _
        _ = r • (f.val.app V).hom (inv V x) :=
          (congrArg (r • ·) (hright V x)).symm
        _ = (f.val.app V).hom (r • inv V x) :=
          ((f.val.app V).hom.map_smul r _).symm
    · intro V W i x
      apply (hbij W).1
      exact (PresheafOfModules.naturality_apply f.val i (inv V x)).trans
        ((congrArg (fun y ↦ B.val.map i y) (hright V x)).trans (hright W _).symm)
  exact { val := {
    app := fun V ↦ @ModuleCat.ofHom (Z.left.ringCatSheaf.obj.obj V) _
      (B.val.obj V) (A.val.obj V)
      (B.val.obj V).isAddCommGroup (B.val.obj V).isModule
      (A.val.obj V).isAddCommGroup (A.val.obj V).isModule {
      toFun := inv V
      map_add' := laws.1 V
      map_smul' := laws.2.1 V }
    naturality := by
      intro V W i
      ext x
      exact (laws.2.2 i x).symm } }

/-- The canonical comparison and its specified inverse give an isomorphism on quasi-coherent inputs. -/
def tensorPowerIso (Z : Over S) (L : (ofOver Z).Modules) [L.IsQuasicoherent] (n : ℕ) : RingedSpace.TensorPower.sheaf ((Modules.restrictToScheme Z).obj L) n ≅ (Modules.restrictToScheme Z).obj (tensorPowerUnit L n) := by
  let hom : RingedSpace.TensorPower.sheaf ((Modules.restrictToScheme Z).obj L) n ⟶ (Modules.restrictToScheme Z).obj (tensorPowerUnit L n) := tensorPowerComparison Z L n
  let inv : (Modules.restrictToScheme Z).obj (tensorPowerUnit L n) ⟶ RingedSpace.TensorPower.sheaf ((Modules.restrictToScheme Z).obj L) n := tensorPowerInverse Z L n
  have laws : hom ≫ inv = 𝟙 _ ∧ inv ≫ hom = 𝟙 _ := by
    constructor
    · apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro V
      ext x
      exact preimageOr_apply 0 _ (tensorPowerComparison_bijective Z L n V).1 x
    · apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro V
      ext x
      exact preimageOr_rightInverse 0 _ (tensorPowerComparison_bijective Z L n V).2 x
  exact ⟨hom, inv, laws.1, laws.2⟩

/-- The recursive tensor-power comparison is invertible on quasi-coherent modules. -/
instance tensorPowerComparison_isIso (Z : Over S) (L : (ofOver Z).Modules) [L.IsQuasicoherent] (n : ℕ) : IsIso (tensorPowerComparison Z L n) :=
  (tensorPowerIso Z L n).isIso_hom

/-- An invertible module on this small etale site is quasi-coherent. -/
theorem invertible_isQuasicoherent (Z : Over S) (L : (ofOver Z).Modules)
    (hL : isInvertibleObject L) : L.IsQuasicoherent := by
  letI := hL
  exact Modules.isQuasicoherent_of_isInvertible L

end AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme

