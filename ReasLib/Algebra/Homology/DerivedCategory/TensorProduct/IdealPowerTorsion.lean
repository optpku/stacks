/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
public import ReasLib.Algebra.Homology.DerivedCategory.TensorProduct
public import ReasLib.Algebra.Module.IdealPower.Predicate
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
import ReasLib.Algebra.Homology.ChainComplex.IdealPowerResolution
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived tensor products with ideal-power torsion

This file owns the nonpositive cohomological bounds and zero-object criteria obtained by
tensoring with ideal-power torsion modules and bounded derived objects.

@stack 0H82
@stack 0G1T
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open scoped DerivedTensorProduct

universe u

namespace CategoryTheory.DerivedCategory.TensorProduct.IdealPowerTorsion

section

variable {R : Type u} [CommRing R] (I : Ideal R)

local notation "DMod" => _root_.DerivedCategory (ModuleCat R)
local notation "H" => _root_.DerivedCategory.homologyFunctor (ModuleCat R)
local notation "RmodI" => ModuleCat.single0Functor.obj (ModuleCat.of R (R ⧸ I))

/-- Lemma 15.89.7 (2): the same nonpositive bound holds after tensoring with any
`I`-power torsion module. -/
@[stacks 0H82 "Lemma 15.89.7 (2)"]
theorem module_isLE_zero
    (K : DMod) (hKI : (K ⊗[R]^L RmodI).IsLE 0)
    (N : ModuleCat R) (hN : Module.IsIdealPowerTorsion I N) :
    (K ⊗[R]^L ModuleCat.single0Functor.obj N).IsLE 0 := sorry
-- Proof strategy: use a K-flat representative to commute tensoring with the filtered union
-- of the submodules annihilated by `I ^ n`; for each stage use the square-zero extension
-- `R / I ^ n ⊕ N` and descent of the nonpositive Tor bound modulo a nilpotent ideal.

/-- Lemma 15.89.7 (1): if tensoring `K` with `R ⧸ I` has no positive cohomology, the
same holds after tensoring with `R ⧸ Iⁿ` for every positive `n`. -/
@[stacks 0H82 "Lemma 15.89.7 (1)"]
theorem quotient_isLE_zero
    (K : DMod) (hKI : (K ⊗[R]^L RmodI).IsLE 0) (n : ℕ+) :
    (K ⊗[R]^L ModuleCat.single0Functor.obj
      (ModuleCat.of R (R ⧸ I ^ (n : ℕ)))).IsLE 0 := by
  apply module_isLE_zero I K hKI
  apply top_unique
  intro x _
  rw [Ideal.primaryComponent_mem]
  refine ⟨(n : ℕ), ?_⟩
  rw [Submodule.mem_torsionBySet_iff]
  intro a
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk (I ^ (n : ℕ)) ((a : R) * r) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.2 ((I ^ (n : ℕ)).mul_mem_right r a.property)

-- Transport torsion using the primary component, without the admitted predicate bridges.
private theorem torsion_of_surjective {N P : ModuleCat R} (f : N ⟶ P)
    (hf : Function.Surjective f) (hN : Module.IsIdealPowerTorsion I N) :
    Module.IsIdealPowerTorsion I P := by
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := hf y
  have hx : x ∈ I.primaryComponent N := by rw [hN]; trivial
  exact I.primaryComponent_map_mem f.hom ⟨x, hx⟩

private theorem torsion_of_injective {N P : ModuleCat R} (f : N ⟶ P)
    (hf : Function.Injective f) (hP : Module.IsIdealPowerTorsion I P) :
    Module.IsIdealPowerTorsion I N := by
  apply top_unique
  intro x _
  have hx : f x ∈ I.primaryComponent P := by rw [hP]; trivial
  rw [Ideal.primaryComponent_mem] at hx ⊢
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  rw [Submodule.mem_torsionBySet_iff] at hn ⊢
  intro a
  apply hf
  simpa using hn a

private theorem torsion_of_isZero (N : ModuleCat R) (hN : IsZero N) :
    Module.IsIdealPowerTorsion I N := by
  apply top_unique
  intro x _
  have hx : x = 0 := by
    simpa using congrArg (fun f : N ⟶ N ↦ f x) (hN.eq_of_src (𝟙 N) 0)
  rw [hx]
  exact Submodule.zero_mem _

private theorem isLE_zero_of_concentrated (F : DMod ⥤ DMod) [F.CommShift ℤ]
    (hF : ∀ N : ModuleCat R, Module.IsIdealPowerTorsion I N →
      (F.obj (ModuleCat.single0Functor.obj N)).IsLE 0)
    (X : DMod) (a : ℤ) (ha : a ≤ 0) (hGE : X.IsGE a) (hLE : X.IsLE a)
    (hX : Module.IsIdealPowerTorsion I ((H a).obj X)) : (F.obj X).IsLE 0 := by
  letI : X.IsGE a := hGE
  letI : X.IsLE a := hLE
  obtain ⟨N, ⟨e⟩⟩ := X.exists_iso_singleFunctor_obj_of_isGE_of_isLE a
  let eH : (H a).obj X ≅ N := (H a).mapIso e ≪≫
    (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) a).app N
  have hN := torsion_of_surjective I eH.hom eH.toLinearEquiv.surjective hX
  let S := ModuleCat.single0Functor.obj N
  haveI : (F.obj S).IsLE 0 := hF N hN
  haveI : ((F.obj S)⟦-a⟧).IsLE a :=
    _root_.DerivedCategory.TStructure.t.isLE_shift (F.obj S) 0 (-a) a (by omega)
  haveI : ((F.obj S)⟦-a⟧).IsLE 0 := _root_.DerivedCategory.TStructure.t.isLE_of_le _ a 0 ha
  let eS : (_root_.DerivedCategory.singleFunctor (ModuleCat R) a).obj N ≅ S⟦-a⟧ :=
    ((_root_.DerivedCategory.singleFunctors (ModuleCat R)).shiftIso (-a) a 0 (by omega)).symm.app N
  let eF : F.obj X ≅ (F.obj S)⟦-a⟧ :=
    F.mapIso (e ≪≫ eS) ≪≫ (F.commShiftIso (-a)).app S
  exact _root_.DerivedCategory.TStructure.t.isLE_of_iso eF.symm 0

-- Induct on the cohomological interval by peeling off its lowest degree.
private theorem isLE_zero_of_homology (F : DMod ⥤ DMod) [F.CommShift ℤ] [F.IsTriangulated]
    (hF : ∀ N : ModuleCat R, Module.IsIdealPowerTorsion I N →
      (F.obj (ModuleCat.single0Functor.obj N)).IsLE 0)
    (n : ℕ) (X : DMod) (hGE : X.IsGE (-(n : ℤ))) (hLE : X.IsLE 0)
    (hX : ∀ i ≤ 0, Module.IsIdealPowerTorsion I ((H i).obj X)) :
    (F.obj X).IsLE 0 := by
  induction n generalizing X with
  | zero =>
    exact isLE_zero_of_concentrated I F hF X 0 le_rfl (by simpa using hGE) hLE (hX 0 le_rfl)
  | succ n ih =>
    let a : ℤ := -((n : ℤ) + 1)
    haveI : X.IsGE a := by simpa [a] using hGE
    haveI : X.IsLE 0 := hLE
    let T : Triangle DMod := (_root_.DerivedCategory.TStructure.t.triangleLTGE (a + 1)).obj X
    have hT : T ∈ distTriang DMod :=
      _root_.DerivedCategory.TStructure.t.triangleLTGE_distinguished (a + 1) X
    let A := T.obj₁
    let B := T.obj₃
    haveI : A.IsGE a := by
      change ((_root_.DerivedCategory.TStructure.t.truncLT (a + 1)).obj X).IsGE a
      infer_instance
    haveI : A.IsLE a := by
      dsimp [A, T]
      exact _root_.DerivedCategory.TStructure.t.isLE_truncLT_obj X (a + 1) a (by omega)
    haveI : B.IsGE (a + 1) := by dsimp [B, T]; infer_instance
    have hBGE : B.IsGE (-(n : ℤ)) :=
      _root_.DerivedCategory.TStructure.t.isGE_of_ge B _ (a + 1) (by dsimp [a]; omega)
    have hBLE : B.IsLE 0 := by
      change ((_root_.DerivedCategory.TStructure.t.truncGE (a + 1)).obj X).IsLE 0
      infer_instance
    let f := (H a).map T.mor₁
    haveI : Mono f :=
      (_root_.DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
        T hT (a - 1) a (by omega)).2
        ((_root_.DerivedCategory.isZero_of_isGE B (a + 1) (a - 1) (by omega)).eq_of_src _ _)
    have hAtors : Module.IsIdealPowerTorsion I ((H a).obj A) :=
      torsion_of_injective I f ((ModuleCat.mono_iff_injective f).1 inferInstance)
        (hX a (by dsimp [a]; omega))
    have hFA : (F.obj A).IsLE 0 :=
      isLE_zero_of_concentrated I F hF A a (by dsimp [a]; omega)
        inferInstance inferInstance hAtors
    have hBtors (i : ℤ) (hi : i ≤ 0) : Module.IsIdealPowerTorsion I ((H i).obj B) := by
      by_cases hbi : a + 1 ≤ i
      · let g := (H i).map T.mor₂
        haveI : Epi g :=
          (_root_.DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff
            T hT i (i + 1) rfl).2
            ((_root_.DerivedCategory.isZero_of_isLE A a (i + 1) (by omega)).eq_of_tgt _ _)
        exact torsion_of_surjective I g ((ModuleCat.epi_iff_surjective g).1 inferInstance) (hX i hi)
      · exact torsion_of_isZero I _
          (_root_.DerivedCategory.isZero_of_isGE B (a + 1) i (by omega))
    exact _root_.DerivedCategory.TStructure.t.isLE₂ (F.mapTriangle.obj T)
      (F.map_distinguished T hT) 0 hFA (ih B hBGE hBLE hBtors)

/-- A reusable form of the bounded-complex clause in which torsion is required only in
nonpositive degrees; the `IsLE 0` hypothesis already forces positive cohomology to vanish. -/
@[stacks 0H82 "bounded nonpositive torsion companion"]
theorem bounded_isLE_zero_of_nonpositive
    (K : DMod) (hKI : (K ⊗[R]^L RmodI).IsLE 0)
    (M : _root_.DerivedCategory.Bounded (ModuleCat R))
    (hMtors : ∀ i ≤ 0, Module.IsIdealPowerTorsion I ((H i).obj M.obj))
    (hMle : M.obj.IsLE 0) :
    (K ⊗[R]^L M.obj).IsLE 0 := by
  let F := derivedTensorProduct K
  letI : F.IsTriangulated := derivedTensorProduct_isTriangulated K
  have hF (N : ModuleCat R) (hN : Module.IsIdealPowerTorsion I N) :
      (F.obj (ModuleCat.single0Functor.obj N)).IsLE 0 := by
    haveI : (K ⊗[R]^L ModuleCat.single0Functor.obj N).IsLE 0 :=
      module_isLE_zero I K hKI N hN
    let e : (K ⊗[R]^L ModuleCat.single0Functor.obj N) ≅ F.obj (ModuleCat.single0Functor.obj N) :=
      DerivedTensorProduct.comm K _
    exact _root_.DerivedCategory.TStructure.t.isLE_of_iso e 0
  obtain ⟨a, ha⟩ := M.property.1
  haveI : M.obj.IsGE a := ha
  have hGE : M.obj.IsGE (-((-a).toNat : ℤ)) :=
    _root_.DerivedCategory.TStructure.t.isGE_of_ge M.obj _ a (by omega)
  haveI : (M.obj ⊗[R]^L K).IsLE 0 :=
    isLE_zero_of_homology I F hF (-a).toNat M.obj hGE hMle hMtors
  exact _root_.DerivedCategory.TStructure.t.isLE_of_iso (DerivedTensorProduct.comm M.obj K) 0

/-- Lemma 15.89.7 (3): if `M ∈ Dᵇ(R)` has `I`-power torsion cohomology and no positive
cohomology, then `K ⊗ᴸ_R M` has no positive cohomology. -/
@[stacks 0H82 "Lemma 15.89.7 (3)"]
theorem bounded_isLE_zero
    (K : DMod) (hKI : (K ⊗[R]^L RmodI).IsLE 0)
    (M : _root_.DerivedCategory.Bounded (ModuleCat R))
    (hMtors : ∀ i : ℤ, Module.IsIdealPowerTorsion I ((H i).obj M.obj))
    (hMle : M.obj.IsLE 0) :
    (K ⊗[R]^L M.obj).IsLE 0 := by
  exact bounded_isLE_zero_of_nonpositive I K hKI M (fun i _ ↦ hMtors i) hMle

private theorem isZero_of_shift_isLE_zero (X : DMod)
    (hX : ∀ n : ℤ, (X⟦n⟧).IsLE 0) : IsZero X := by
  have hle (n : ℤ) : X.IsLE n :=
    (_root_.DerivedCategory.TStructure.t.isLE_shift_iff X n n 0 (add_zero n)).1 (hX n)
  have : X.IsLE 0 := hle 0
  have : X.IsGE 1 := by
    rw [_root_.DerivedCategory.isGE_iff]
    intro i _
    exact (_root_.DerivedCategory.isLE_iff X (i - 1)).1 (hle (i - 1)) i (by omega)
  exact _root_.DerivedCategory.TStructure.t.isZero X 0 1

-- Apply the nonpositive bound to every shift of the left tensor factor.
private theorem tensor_isZero_of_isLE_zero
    (K N : DMod) (hKI : IsZero (K ⊗[R]^L RmodI))
    (hN : ∀ L : DMod, (L ⊗[R]^L RmodI).IsLE 0 → (L ⊗[R]^L N).IsLE 0) :
    IsZero (K ⊗[R]^L N) := by
  apply isZero_of_shift_isLE_zero
  intro n
  have hKI' : IsZero (K⟦n⟧ ⊗[R]^L RmodI) :=
    ((shiftFunctor DMod n).map_isZero hKI).of_iso
      (((derivedTensorProduct RmodI).commShiftIso n).app K)
  haveI : (K⟦n⟧ ⊗[R]^L N).IsLE 0 :=
    hN (K⟦n⟧) (_root_.DerivedCategory.TStructure.t.isLE_of_isZero hKI' 0)
  let e : (K⟦n⟧ ⊗[R]^L N) ≅ (K ⊗[R]^L N)⟦n⟧ :=
    ((derivedTensorProduct N).commShiftIso n).app K
  exact _root_.DerivedCategory.TStructure.t.isLE_of_iso e 0

/-- Lemma 15.89.8 (1): if `K ⊗ᴸ_R (R ⧸ I)` is zero, then
`K ⊗ᴸ_R (R ⧸ Iⁿ)` is zero for every positive `n`. -/
@[stacks 0G1T "Lemma 15.89.8 (1)"]
theorem quotient_isZero
    (K : DMod) (hKI : IsZero (K ⊗[R]^L RmodI)) (n : ℕ+) :
    IsZero (K ⊗[R]^L ModuleCat.single0Functor.obj
      (ModuleCat.of R (R ⧸ I ^ (n : ℕ)))) := by
  exact tensor_isZero_of_isLE_zero I K _ hKI (fun L hL ↦ quotient_isLE_zero I L hL n)

/-- Lemma 15.89.8 (2): if `K ⊗ᴸ_R (R ⧸ I)` is zero, then `K ⊗ᴸ_R N` is
zero for every `I`-power torsion module `N`. -/
@[stacks 0G1T "Lemma 15.89.8 (2)"]
theorem module_isZero
    (K : DMod) (hKI : IsZero (K ⊗[R]^L RmodI))
    (N : ModuleCat R) (hN : Module.IsIdealPowerTorsion I N) :
    IsZero (K ⊗[R]^L ModuleCat.single0Functor.obj N) := by
  exact tensor_isZero_of_isLE_zero I K _ hKI (fun L hL ↦ module_isLE_zero I L hL N hN)

/-- Lemma 15.89.8 (3): if `K ⊗ᴸ_R (R ⧸ I)` is zero, then `K ⊗ᴸ_R M` is
zero for every bounded derived object `M` whose cohomology is `I`-power torsion. -/
@[stacks 0G1T "Lemma 15.89.8 (3)"]
theorem bounded_isZero
    (K : DMod) (hKI : IsZero (K ⊗[R]^L RmodI))
    (M : _root_.DerivedCategory.Bounded (ModuleCat R))
    (hMtors : ∀ i : ℤ, Module.IsIdealPowerTorsion I ((H i).obj M.obj)) :
    IsZero (K ⊗[R]^L M.obj) := by
  obtain ⟨b, hb⟩ := M.property.2
  haveI : M.obj.IsLE b := hb
  let M' : _root_.DerivedCategory.Bounded (ModuleCat R) :=
    ⟨M.obj⟦b⟧, ObjectProperty.le_shift _ b _ M.property⟩
  have hM'le : M'.obj.IsLE 0 :=
    _root_.DerivedCategory.TStructure.t.isLE_shift M.obj b b 0 (add_zero b)
  have hM'tors (i : ℤ) : Module.IsIdealPowerTorsion I ((H i).obj M'.obj) := by
    let e : (H i).obj M'.obj ≅ (H (b + i)).obj M.obj :=
      ((H 0).shiftIso b i (b + i) rfl).app M.obj
    apply top_unique
    intro y _
    have hx : e.hom y ∈ I.primaryComponent ((H (b + i)).obj M.obj) := by
      rw [hMtors (b + i)]
      trivial
    simpa using I.primaryComponent_map_mem e.inv.hom ⟨e.hom y, hx⟩
  have hzero : IsZero (K ⊗[R]^L M'.obj) :=
    tensor_isZero_of_isLE_zero I K _ hKI
      (fun L hL ↦ bounded_isLE_zero I L hL M' hM'tors hM'le)
  let e : (K ⊗[R]^L M'.obj) ≅ (K ⊗[R]^L M.obj)⟦b⟧ :=
    DerivedTensorProduct.comm K M'.obj ≪≫
      ((derivedTensorProduct K).commShiftIso b).app M.obj ≪≫
      (shiftFunctor DMod b).mapIso (DerivedTensorProduct.comm M.obj K)
  exact ((shiftFunctor DMod (-b)).map_isZero (hzero.of_iso e.symm)).of_iso
    ((shiftEquiv DMod b).unitIso.app (K ⊗[R]^L M.obj))

end

end CategoryTheory.DerivedCategory.TensorProduct.IdealPowerTorsion
