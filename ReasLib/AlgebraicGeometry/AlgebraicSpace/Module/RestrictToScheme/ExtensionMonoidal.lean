/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.Extension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.Monoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorPower

/-! # Unit and tensor comparisons for extension to the small étale site -/
@[expose] public section
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.RelativeProj
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme
variable {S : Scheme.{u}} (Z : Over S)

/-- The oplax unit and tensor maps are the adjunction mates of restriction's lax maps. -/
instance extensionOplaxMonoidal : (extension Z).OplaxMonoidal :=
  (extensionAdjunction Z).leftAdjointOplaxMonoidal

/-- The inverse unit map selects preimages of the canonical unit mate, with zero fallback. -/
def extensionUnitInverse :
    𝟙_ (ofOver Z).Modules ⟶ (extension Z).obj (𝟙_ Z.left.Modules) := by
  let A : (ofOver Z).Modules := (extension Z).obj (𝟙_ Z.left.Modules)
  let B : (ofOver Z).Modules := 𝟙_ (ofOver Z).Modules
  let f : A ⟶ B := Functor.OplaxMonoidal.η (extension Z)
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

/-- The canonical unit mate and its specified inverse form the extension unit isomorphism. -/
def extensionUnitIso : (extension Z).obj (𝟙_ Z.left.Modules) ≅ 𝟙_ (ofOver Z).Modules := by
  let hom : (extension Z).obj (𝟙_ Z.left.Modules) ⟶ 𝟙_ (ofOver Z).Modules := Functor.OplaxMonoidal.η (extension Z)
  let inv : 𝟙_ (ofOver Z).Modules ⟶ (extension Z).obj (𝟙_ Z.left.Modules) := extensionUnitInverse Z
  have laws : hom ≫ inv = 𝟙 _ ∧ inv ≫ hom = 𝟙 _ := by sorry
  exact ⟨hom, inv, laws.1, laws.2⟩

/-- The specified extension unit mate is invertible. -/
instance extensionUnit_isIso : IsIso (Functor.OplaxMonoidal.η (extension Z)) :=
  (extensionUnitIso Z).isIso_hom

/-- The inverse tensor map selects preimages of the canonical tensor mate, with zero fallback. -/
def extensionTensorInverse (M N : Z.left.Modules) :
    (extension Z).obj M ⊗ (extension Z).obj N ⟶ (extension Z).obj (M ⊗ N) := by
  let A : (ofOver Z).Modules := (extension Z).obj (M ⊗ N)
  let B : (ofOver Z).Modules := (extension Z).obj M ⊗ (extension Z).obj N
  let f : A ⟶ B := Functor.OplaxMonoidal.δ (extension Z) M N
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

/-- The canonical tensor mate and its specified inverse form the extension tensor isomorphism. -/
def extensionTensorIso (M N : Z.left.Modules) : (extension Z).obj (M ⊗ N) ≅ (extension Z).obj M ⊗ (extension Z).obj N := by
  let hom : (extension Z).obj (M ⊗ N) ⟶ (extension Z).obj M ⊗ (extension Z).obj N := Functor.OplaxMonoidal.δ (extension Z) M N
  let inv : (extension Z).obj M ⊗ (extension Z).obj N ⟶ (extension Z).obj (M ⊗ N) := extensionTensorInverse Z M N
  have laws : hom ≫ inv = 𝟙 _ ∧ inv ≫ hom = 𝟙 _ := by sorry
  exact ⟨hom, inv, laws.1, laws.2⟩

/-- The specified extension tensor mate is invertible. -/
instance extensionTensor_isIso (M N : Z.left.Modules) :
    IsIso (Functor.OplaxMonoidal.δ (extension Z) M N) :=
  (extensionTensorIso Z M N).isIso_hom

/-- Extension is strong monoidal through the inverses of its specified adjunction mates. -/
instance extensionMonoidal : (extension Z).Monoidal :=
  Functor.Monoidal.ofOplaxMonoidal (extension Z)

/-- Extension of tensor powers is obtained recursively from its unit and tensor comparisons. -/
def extensionTensorPowerIso (L : Z.left.Modules) (n : ℕ) :
    (extension Z).obj (RingedSpace.TensorPower.sheaf L n) ≅
      tensorPowerUnit ((extension Z).obj L) n :=
  match n with
  | 0 =>
      (extension Z).mapIso (eqToIso (RingedSpace.TensorPower.zero L)) ≪≫
        (extension Z).mapIso (RingedSpace.unitIsoTensorUnit Z.left.toRingedSpace) ≪≫
          extensionUnitIso Z ≪≫ (Modules.structureModuleIsoTensorUnit (ofOver Z)).symm
  | n + 1 =>
      (extension Z).mapIso (eqToIso (RingedSpace.TensorPower.succ L n)) ≪≫
        extensionTensorIso Z L (RingedSpace.TensorPower.sheaf L n) ≪≫
          (Iso.refl _ ⊗ᵢ extensionTensorPowerIso L n)

end AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme
