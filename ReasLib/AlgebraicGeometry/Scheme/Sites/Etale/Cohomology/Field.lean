/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.GaloisModule
public import ReasLib.AlgebraicGeometry.Scheme.Etale.StalkFunctor
public import ReasLib.FieldTheory.Galois.Cohomology.Coefficients
public import ReasLib.FieldTheory.Galois.Cohomology.Units
public import ReasLib.FieldTheory.Galois.Cohomology.Vanishing
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.DerivedInvariants
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.UniqueFactorization
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Affine
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Action ModuleCat
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale.Small

universe u

noncomputable section

namespace GaloisCohomology

variable (K Ksep : Type u) [Field K] [Field Ksep]
  [Algebra K Ksep] [IsSepClosure K Ksep]

/-- The geometric stalk of the constant `ZMod n` sheaf is the trivial discrete Galois module. -/
theorem constantZModEtaleStalk (n : ℕ)
    [HasWeakSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}] :
    IsIsomorphic
      (etaleStalk K Ksep
        ((constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} (ZMod n)))))
      (constantZModModule K Ksep n) := by
  let Φ := etalePoint K Ksep
  let A := AddCommGrpCat.of (ULift.{u} (ZMod n))
  let P := (Functor.const (Spec (.of K)).Etaleᵒᵖ).obj A
  let D := (Functor.const Φ.fiber.Elementsᵒᵖ).obj A
  let e₀ : Φ.presheafFiber.obj P ≅ A :=
    (colimit.isColimit D).coconePointUniqueUpToIso (isColimitConstCocone _ A)
  have hι (U : (Spec (.of K)).Etale) (x : Φ.fiber.obj U) :
      Φ.toPresheafFiber U x P ≫ e₀.hom = 𝟙 A := by
    exact (colimit.isColimit D).comp_coconePointUniqueUpToIso_hom
      (isColimitConstCocone _ A) (op ⟨U, x⟩)
  let e : etaleFiber K Ksep
      ((constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}).obj A) ≅ A :=
    (Φ.presheafToSheafCompSheafFiberIso AddCommGrpCat.{u}).app P ≪≫ e₀
  refine ⟨(openStabilizer ℤ (Gal(Ksep / K))).isoMk
    (Action.mkIso e.addCommGroupIsoToAddEquiv.toIntLinearEquiv.toModuleIso ?_)⟩
  intro sigma
  let α := GrothendieckTopology.Point.Hom.presheafFiber
    (A := AddCommGrpCat.{u})
    (⟨etaleFiberAction K Ksep sigma⟩ : Φ ⟶ Φ)
  have hP : α.app P = 𝟙 _ := by
    apply Φ.presheafFiber_hom_ext
    intro U x
    apply (cancel_mono e₀.hom).mp
    simp only [α, GrothendieckTopology.Point.Hom.presheafFiber_app,
      GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc,
      Category.comp_id, hι]
  have hF : α.app (sheafify (Spec (.of K)).smallEtaleTopology P) = 𝟙 _ := by
    apply (cancel_epi (Φ.presheafFiber.map
      (toSheafify (Spec (.of K)).smallEtaleTopology P))).mp
    rw [α.naturality, hP]
    simp
  change ModuleCat.ofHom (α.app (sheafify (Spec (.of K)).smallEtaleTopology P)).hom.toIntLinearMap ≫
    _ = _ ≫ 𝟙 _
  rw [hF]
  rfl

/-- The geometric stalk of the units sheaf is the natural Galois module on separable-closure
units, written additively. -/
theorem unitsEtaleStalk :
    IsIsomorphic (etaleStalk K Ksep (unitsAddSheaf (Spec (.of K))))
      (unitsModule K Ksep) := sorry

/-- The geometric stalk of the additive structure sheaf is the additive Galois module on the
separable closure. -/
theorem additiveEtaleStalk :
    IsIsomorphic
      (etaleStalk K Ksep
        ((sheafCompose (Spec (.of K)).smallEtaleTopology
          (forget₂ RingCat AddCommGrpCat)).obj (structureSheaf (Spec (.of K)))))
      (additiveModule K Ksep) := sorry

attribute [-instance] etaleStalkFunctorIsEquivalence in
/-- The geometric stalk of the kernel of multiplication by `n` on the additive units sheaf is
the Galois module on the `n`th roots of unity. -/
theorem rootsOfUnityEtaleStalk (n : ℕ) :
    IsIsomorphic
      (etaleStalk K Ksep (kernel (n • 𝟙 (unitsAddSheaf (Spec (.of K))))))
      (rootsOfUnityModule K Ksep n) := by
  let T := etaleStalkFunctor K Ksep
  let V := (openStabilizer ℤ (Gal(Ksep / K))).ι ⋙
    Action.forget (ModuleCat ℤ) (Gal(Ksep / K))
  let W := V ⋙ forget₂ (ModuleCat ℤ) AddCommGrpCat
  have hTW : T ⋙ W = (etalePoint K Ksep).sheafFiber := by rfl
  letI : PreservesFiniteLimits (T ⋙ W) := by rw [hTW]; infer_instance
  letI : PreservesFiniteLimits T := preservesFiniteLimits_of_reflects_of_preserves T W
  letI : T.Additive := Functor.additive_of_preserves_binary_products T
  let U := unitsModule K Ksep
  let R := rootsOfUnityModule K Ksep n
  let j : R ⟶ U := ObjectProperty.homMk
    { hom := ModuleCat.ofHom (rootsOfUnity n Ksep).subtype.toAdditive.toIntLinearMap
      comm := fun sigma ↦ by ext x; rfl }
  have w : j ≫ (n • 𝟙 U) = 0 := by
    apply ObjectProperty.hom_ext
    apply Action.hom_injective
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change n • Additive.ofMul (Additive.toMul x).val = 0
    rw [← ofMul_pow, (Additive.toMul x).property]
    rfl
  have hex : Function.Exact j.hom.hom.hom (n • 𝟙 U).hom.hom.hom := by
    change Function.Exact
      (fun x : Additive (rootsOfUnity n Ksep) ↦ Additive.ofMul (Additive.toMul x).val)
      (fun y : Additive Ksepˣ ↦ n • y)
    intro y
    change n • y = 0 ↔ ∃ x : Additive (rootsOfUnity n Ksep),
      Additive.ofMul (Additive.toMul x).val = y
    constructor
    · intro hy
      refine ⟨Additive.ofMul ⟨Additive.toMul y, ?_⟩, rfl⟩
      simpa only [mem_rootsOfUnity, toMul_nsmul, toMul_zero] using
        congrArg Additive.toMul hy
    · rintro ⟨x, rfl⟩
      rw [← ofMul_pow, (Additive.toMul x).property]
      rfl
  have hinj : Function.Injective j.hom.hom.hom := by
    intro x y h
    exact congrArg Additive.ofMul (Subtype.ext h)
  have hR : IsLimit (KernelFork.ofι j w) := by
    apply isLimitOfReflects V
    refine (isLimitMapConeForkEquiv' V w).symm ?_
    exact ModuleCat.isLimitKernelFork j.hom.hom (n • 𝟙 U).hom.hom hex hinj
  obtain ⟨e⟩ := unitsEtaleStalk K Ksep
  refine ⟨PreservesKernel.iso T (n • 𝟙 (unitsAddSheaf (Spec (.of K)))) ≪≫
    kernel.mapIso _ (n • 𝟙 U) e e (by simp) ≪≫
    (kernelIsKernel (n • 𝟙 U)).conePointUniqueUpToIso hR⟩

/-- Small étale cohomology of the units sheaf over a field agrees with derived-invariants
Galois cohomology of separable-closure units. -/
theorem etaleUnitsCohomologyIsomorphicGalois (i : ℕ)
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})] :
    IsIsomorphic
      ((Sheaf.functorH (Spec (.of K)).smallEtaleTopology i).obj
        (unitsAddSheaf (Spec (.of K))))
      ((forget₂ (ModuleCat ℤ) AddCommGrpCat).obj
        ((DiscreteModuleCat.derivedCohomologyFunctor ℤ (Gal(Ksep / K)) i).obj
          (unitsModule K Ksep))) := sorry

/-- Small étale cohomology of the additive structure sheaf over a field agrees with
derived-invariants Galois cohomology of the additive separable closure. -/
theorem etaleAdditiveCohomologyIsomorphicGalois (i : ℕ)
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})] :
    IsIsomorphic
      ((Sheaf.functorH (Spec (.of K)).smallEtaleTopology i).obj
        ((sheafCompose (Spec (.of K)).smallEtaleTopology
          (forget₂ RingCat AddCommGrpCat)).obj (structureSheaf (Spec (.of K)))))
      ((forget₂ (ModuleCat ℤ) AddCommGrpCat).obj
        ((DiscreteModuleCat.derivedCohomologyFunctor ℤ (Gal(Ksep / K)) i).obj
          (additiveModule K Ksep))) := sorry

/-- First small étale cohomology of the units sheaf over the spectrum of a field vanishes. -/
theorem etaleH1UnitsIsZero
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})] :
    IsZero ((Sheaf.functorH (Spec (.of K)).smallEtaleTopology 1).obj
      (unitsAddSheaf (Spec (.of K)))) := by
  obtain ⟨e⟩ := Scheme.h1EtaleUnitsIsomorphicPicard (Spec (.of K))
  exact IsZero.of_full_of_faithful_of_isZero AddCommGrpCat.uliftFunctor _
    ((AddCommGrpCat.isZero_of_subsingleton
      (AddCommGrpCat.of (Spec (.of K)).PicardGroup)).of_iso e)

/-- Positive-degree small étale cohomology of the additive structure sheaf over a field
vanishes. -/
theorem etaleAdditiveCohomologyIsZero (i : ℕ) (hi : 0 < i)
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})] :
    IsZero ((Sheaf.functorH (Spec (.of K)).smallEtaleTopology i).obj
      ((sheafCompose (Spec (.of K)).smallEtaleTopology
        (forget₂ RingCat AddCommGrpCat)).obj (structureSheaf (Spec (.of K))))) := by
  obtain ⟨e⟩ := etaleAdditiveCohomologyIsomorphicGalois K (SeparableClosure K) i
  exact (Functor.map_isZero (forget₂ (ModuleCat ℤ) AddCommGrpCat)
    (additiveCohomologyIsZero K (SeparableClosure K) i hi)).of_iso e

end GaloisCohomology

end
