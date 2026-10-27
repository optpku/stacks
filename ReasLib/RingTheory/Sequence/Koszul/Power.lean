/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Embedding.DownNat
public import ReasLib.RingTheory.Sequence.Koszul.Family
public import ReasLib.RingTheory.Sequence.Koszul.Functoriality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Powers of finite-family Koszul complexes

This file separates the Koszul complex on the exact powers `f i ^ n` from the zero-based indexing
of the usual inverse system, whose stage `n` uses `f i ^ (n + 1)`. For `n ≤ m`, the transition
from exponent `m` to exponent `n` is induced by the explicit diagonal map multiplying coordinate
`i` by `f i ^ (m - n)`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

universe u v

variable {R : Type u} [CommRing R]

namespace KoszulComplex

/-- The linear form determined by the exact `n`th powers of a finite family. -/
@[stacks 0GZJ "exact-power Koszul linear forms"]
abbrev powLinearForm {ι : Type v} [Finite ι] (f : ι → R) (n : ℕ) :
    (ι → R) →ₗ[R] R :=
  koszulLinearForm (fun i ↦ f i ^ n)

/-- The diagonal linear map from exponent `m` toward exponent `n`, multiplying coordinate `i`
by `f i ^ (m - n)`. The order condition belongs to its compatibility theorem, not to this
underlying linear datum. -/
@[stacks 0GZJ "linear map underlying exact-power Koszul transitions"]
def powMapLinear {ι : Type v} (f : ι → R) (n m : ℕ) :
    (ι → R) →ₗ[R] (ι → R) :=
  LinearMap.pi fun i ↦ (f i ^ (m - n)) • LinearMap.proj i

/-- The exact-power diagonal map acts coordinatewise by `f i ^ (m - n)`. -/
@[simp]
theorem powMapLinear_apply {ι : Type v} (f : ι → R) (n m : ℕ)
    (x : ι → R) (i : ι) :
    powMapLinear f n m x i = f i ^ (m - n) * x i := by
  rfl

/-- The exact-power diagonal map intertwines the linear forms at exponents `m` and `n`. -/
@[stacks 0GZJ "compatibility of exact-power Koszul transitions"]
theorem powMapLinear_compatible {ι : Type v} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    (powLinearForm f n).comp (powMapLinear f n m) = powLinearForm f m := by
  classical
  letI := Fintype.ofFinite ι
  apply LinearMap.ext
  intro x
  change Module.piEquiv ι R R (fun i ↦ f i ^ n) (powMapLinear f n m x) =
    Module.piEquiv ι R R (fun i ↦ f i ^ m) x
  simp only [Module.piEquiv_apply_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [powMapLinear_apply]
  calc
    (f i ^ (m - n) * x i) * f i ^ n = x i * (f i ^ (m - n) * f i ^ n) := by
      ac_rfl
    _ = x i * f i ^ m := by rw [← pow_add, Nat.sub_add_cancel h]

/-- The diagonal map at a reflexive exponent inequality is the identity. -/
@[simp]
theorem powMapLinear_refl {ι : Type v} (f : ι → R) (n : ℕ) :
    powMapLinear f n n = LinearMap.id := by
  ext x i
  simp

/-- Exact-power diagonal maps compose according to transitivity of exponent inequalities. -/
theorem powMapLinear_comp {ι : Type v} (f : ι → R) {n m l : ℕ}
    (h_nm : n ≤ m) (h_ml : m ≤ l) :
    (powMapLinear f n m).comp (powMapLinear f m l) = powMapLinear f n l := by
  ext x i
  simp only [LinearMap.comp_apply, powMapLinear_apply]
  rw [← mul_assoc, ← pow_add, show m - n + (l - m) = l - n by omega]

/-- The Koszul complex formed from the exact `n`th powers of a finite family. -/
@[stacks 0GZJ "exact-power Koszul complex"]
abbrev powComplex {ι : Type v} [Finite ι] (f : ι → R) (n : ℕ) :
    ChainComplex (ModuleCat R) ℕ :=
  koszulComplex (powLinearForm f n)

/-- The degree-`k` exterior-power component of the exact-power diagonal map.  It is independent of
the proof that the source exponent is no larger than the target exponent. -/
@[stacks 0GZJ "degreewise exact-power Koszul transition"]
noncomputable def powMapComponent {ι : Type v} (f : ι → R) (n m k : ℕ) :
    (ModuleCat.of R (ι → R)).exteriorPower k ⟶
      (ModuleCat.of R (ι → R)).exteriorPower k :=
  mapComponent (powMapLinear f n m) k

/-- For `n ≤ m`, the canonical chain map from the `m`th-power Koszul complex to the
`n`th-power Koszul complex. -/
@[stacks 0GZJ "exact-power Koszul transition"]
noncomputable def powMap {ι : Type v} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    powComplex f m ⟶ powComplex f n :=
  map (powMapLinear f n m) (powMapLinear_compatible f h)

/-- The degree components of an exact-power transition are the exterior-power maps induced by
its diagonal linear map. -/
@[simp]
theorem powMap_f {ι : Type v} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) (k : ℕ) :
    (powMap f h).f k = powMapComponent f n m k := by
  rfl

/-- The exact-power transition associated to reflexivity is the identity chain map. -/
@[simp]
theorem powMap_refl {ι : Type v} [Finite ι] (f : ι → R) (n : ℕ) :
    powMap f (le_refl n) = 𝟙 (powComplex f n) := by
  apply HomologicalComplex.Hom.ext
  funext k
  change mapComponent (powMapLinear f n n) k = 𝟙 _
  rw [powMapLinear_refl]
  exact (ModuleCat.exteriorPower.functor R k).map_id _

/-- Exact-power Koszul transitions compose according to transitivity of exponent inequalities. -/
theorem powMap_comp {ι : Type v} [Finite ι] (f : ι → R) {n m l : ℕ}
    (h_nm : n ≤ m) (h_ml : m ≤ l) :
    powMap f h_ml ≫ powMap f h_nm = powMap f (h_nm.trans h_ml) := by
  apply HomologicalComplex.Hom.ext
  funext k
  change (ModuleCat.exteriorPower.functor R k).map (ModuleCat.ofHom (powMapLinear f m l)) ≫
    (ModuleCat.exteriorPower.functor R k).map (ModuleCat.ofHom (powMapLinear f n m)) = _
  rw [← CategoryTheory.Functor.map_comp]
  change mapComponent ((powMapLinear f n m).comp (powMapLinear f m l)) k =
    mapComponent (powMapLinear f n l) k
  rw [powMapLinear_comp f h_nm h_ml]

namespace Reindex

/-- Reindexing a finite family transports its exact-power Koszul linear form along
`LinearEquiv.piCongrLeft'`. -/
@[stacks 0GZJ "reindexed exact-power linear-form compatibility"]
theorem powLinearForm_reindex {ι κ : Type v} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    (powLinearForm (fun j ↦ f (e.symm j)) n).comp
        (LinearEquiv.piCongrLeft' R (fun _ : ι ↦ R) e).toLinearMap =
      powLinearForm f n := by
  classical
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite κ
  apply LinearMap.ext
  intro x
  change Module.piEquiv κ R R (fun j ↦ f (e.symm j) ^ n)
      ((LinearEquiv.piCongrLeft' R (fun _ : ι ↦ R) e) x) =
    Module.piEquiv ι R R (fun i ↦ f i ^ n) x
  simp only [Module.piEquiv_apply_apply]
  exact e.symm.sum_comp (fun i ↦ x i • f i ^ n)

/-- The inverse coordinate reindexing transports the target exact-power linear form back. -/
@[stacks 0GZJ "inverse reindexed exact-power linear-form compatibility"]
theorem powLinearForm_reindex_symm {ι κ : Type v} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    (powLinearForm f n).comp
        (LinearEquiv.piCongrLeft' R (fun _ : ι ↦ R) e).symm.toLinearMap =
      powLinearForm (fun j ↦ f (e.symm j)) n := by
  classical
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite κ
  apply LinearMap.ext
  intro x
  change Module.piEquiv ι R R (fun i ↦ f i ^ n)
      ((LinearEquiv.piCongrLeft' R (fun _ : ι ↦ R) e).symm x) =
    Module.piEquiv κ R R (fun j ↦ f (e.symm j) ^ n) x
  simp only [Module.piEquiv_apply_apply]
  apply Fintype.sum_equiv e
  intro i
  simp [LinearEquiv.piCongrLeft']

/-- The chain map induced by reindexing a finite exact-power Koszul family. -/
@[stacks 0GZJ "reindexing map of exact-power Koszul complexes"]
noncomputable def chainHom {ι κ : Type v} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    powComplex f n ⟶ powComplex (fun j ↦ f (e.symm j)) n :=
  map (LinearEquiv.piCongrLeft' R (fun _ : ι ↦ R) e).toLinearMap
    (powLinearForm_reindex f e n)

/-- The inverse chain map induced by the inverse coordinate reindexing. -/
@[stacks 0GZJ "inverse reindexing map of exact-power Koszul complexes"]
noncomputable def chainInv {ι κ : Type v} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    powComplex (fun j ↦ f (e.symm j)) n ⟶ powComplex f n :=
  map (LinearEquiv.piCongrLeft' R (fun _ : ι ↦ R) e).symm.toLinearMap
    (powLinearForm_reindex_symm f e n)

/-- Reindexing followed by its inverse is the identity on the exact-power Koszul complex. -/
theorem chainHom_inv_id {ι κ : Type v} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    chainHom f e n ≫ chainInv f e n = 𝟙 (powComplex f n) := by
  apply HomologicalComplex.Hom.ext
  funext k
  change (ModuleCat.exteriorPower.functor R k).map
      (ModuleCat.ofHom (LinearEquiv.piCongrLeft' R (fun _ : ι ↦ R) e).toLinearMap) ≫
    (ModuleCat.exteriorPower.functor R k).map
      (ModuleCat.ofHom (LinearEquiv.piCongrLeft' R (fun _ : ι ↦ R) e).symm.toLinearMap) = _
  rw [← CategoryTheory.Functor.map_comp]
  change (ModuleCat.exteriorPower.functor R k).map (ModuleCat.ofHom
    ((LinearEquiv.piCongrLeft' R (fun _ : ι ↦ R) e).symm.toLinearMap.comp
      (LinearEquiv.piCongrLeft' R (fun _ : ι ↦ R) e).toLinearMap)) = _
  rw [LinearEquiv.symm_comp, ModuleCat.ofHom_id]
  exact (ModuleCat.exteriorPower.functor R k).map_id _

/-- The inverse reindexing map followed by reindexing is the identity on the target complex. -/
theorem chainInv_hom_id {ι κ : Type v} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    chainInv f e n ≫ chainHom f e n =
      𝟙 (powComplex (fun j ↦ f (e.symm j)) n) := by
  apply HomologicalComplex.Hom.ext
  funext k
  change (ModuleCat.exteriorPower.functor R k).map
      (ModuleCat.ofHom (LinearEquiv.piCongrLeft' R (fun _ : ι ↦ R) e).symm.toLinearMap) ≫
    (ModuleCat.exteriorPower.functor R k).map
      (ModuleCat.ofHom (LinearEquiv.piCongrLeft' R (fun _ : ι ↦ R) e).toLinearMap) = _
  rw [← CategoryTheory.Functor.map_comp]
  change (ModuleCat.exteriorPower.functor R k).map (ModuleCat.ofHom
    ((LinearEquiv.piCongrLeft' R (fun _ : ι ↦ R) e).toLinearMap.comp
      (LinearEquiv.piCongrLeft' R (fun _ : ι ↦ R) e).symm.toLinearMap)) = _
  rw [LinearEquiv.comp_symm, ModuleCat.ofHom_id]
  exact (ModuleCat.exteriorPower.functor R k).map_id _

/-- The canonical chain-complex isomorphism induced by a finite reindexing. -/
@[stacks 0GZJ "reindexing isomorphism of exact-power Koszul complexes"]
noncomputable def chainIso {ι κ : Type v} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    powComplex f n ≅ powComplex (fun j ↦ f (e.symm j)) n where
  hom := chainHom f e n
  inv := chainInv f e n
  hom_inv_id := chainHom_inv_id f e n
  inv_hom_id := chainInv_hom_id f e n

/-- The forward component of the chain reindexing is its explicit Koszul map. -/
@[simp]
theorem chainIso_hom {ι κ : Type v} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    (chainIso f e n).hom = chainHom f e n := by
  rfl

/-- The inverse component of the chain reindexing is its explicit inverse Koszul map. -/
@[simp]
theorem chainIso_inv {ι κ : Type v} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    (chainIso f e n).inv = chainInv f e n := by
  rfl

end Reindex

/-- The exact-power Koszul complex bundled as its canonical commutative differential graded
algebra. -/
@[stacks 0GZJ "exact-power Koszul commutative differential graded algebra"]
noncomputable abbrev powAlgebra {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    CommMon (ChainComplex (ModuleCat R) ℕ) :=
  commMon (powLinearForm f n)

/-- Forgetting multiplication from an exact-power Koszul algebra recovers its chain complex. -/
@[simp]
theorem powAlgebra_X {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    (powAlgebra f n).X = powComplex f n := by
  rfl

/-- For `n ≤ m`, the exact-power Koszul transition as a morphism of commutative differential
graded algebras. -/
@[stacks 0GZJ "multiplicative exact-power Koszul transition"]
noncomputable def powAlgebraMap {ι : Type u} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    powAlgebra f m ⟶ powAlgebra f n :=
  commMonMap (powMapLinear f n m) (powMapLinear_compatible f h)

/-- The underlying chain map of a multiplicative exact-power transition is `powMap`. -/
@[simp]
theorem powAlgebraMap_hom {ι : Type u} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    (powAlgebraMap f h).hom.hom = powMap f h := by
  rfl

/-- The multiplicative exact-power transition attached to reflexivity is the identity. -/
@[simp]
theorem powAlgebraMap_refl {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    powAlgebraMap f (le_refl n) = 𝟙 (powAlgebra f n) := by
  apply CommMon.hom_ext
  exact powMap_refl f n

/-- Multiplicative exact-power transitions compose according to transitivity. -/
theorem powAlgebraMap_comp {ι : Type u} [Finite ι] (f : ι → R) {n m l : ℕ}
    (h_nm : n ≤ m) (h_ml : m ≤ l) :
    powAlgebraMap f h_ml ≫ powAlgebraMap f h_nm =
      powAlgebraMap f (h_nm.trans h_ml) := by
  apply CommMon.hom_ext
  exact powMap_comp f h_nm h_ml

namespace Reindex

/-- The commutative Koszul-algebra map induced by reindexing a finite exact-power family. -/
@[stacks 0GZJ "reindexing map of exact-power Koszul algebras"]
noncomputable def algebraHom {ι κ : Type u} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    powAlgebra f n ⟶ powAlgebra (fun j ↦ f (e.symm j)) n :=
  commMonMap (LinearEquiv.piCongrLeft' R (fun _ : ι ↦ R) e).toLinearMap
    (powLinearForm_reindex f e n)

/-- The inverse commutative Koszul-algebra map induced by the inverse coordinate reindexing. -/
@[stacks 0GZJ "inverse reindexing map of exact-power Koszul algebras"]
noncomputable def algebraInv {ι κ : Type u} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    powAlgebra (fun j ↦ f (e.symm j)) n ⟶ powAlgebra f n :=
  commMonMap (LinearEquiv.piCongrLeft' R (fun _ : ι ↦ R) e).symm.toLinearMap
    (powLinearForm_reindex_symm f e n)

/-- The underlying chain map of the forward algebra reindexing is the canonical chain map. -/
@[simp]
theorem algebraHom_hom {ι κ : Type u} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    (algebraHom f e n).hom.hom = chainHom f e n := by
  rfl

/-- The underlying chain map of the inverse algebra reindexing is the canonical inverse map. -/
@[simp]
theorem algebraInv_hom {ι κ : Type u} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    (algebraInv f e n).hom.hom = chainInv f e n := by
  rfl

/-- Forward algebra reindexing followed by its inverse is the identity. -/
theorem algebraHom_inv_id {ι κ : Type u} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    algebraHom f e n ≫ algebraInv f e n = 𝟙 (powAlgebra f n) := by
  apply CommMon.hom_ext
  exact chainHom_inv_id f e n

/-- Inverse algebra reindexing followed by reindexing is the identity. -/
theorem algebraInv_hom_id {ι κ : Type u} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    algebraInv f e n ≫ algebraHom f e n =
      𝟙 (powAlgebra (fun j ↦ f (e.symm j)) n) := by
  apply CommMon.hom_ext
  exact chainInv_hom_id f e n

/-- The canonical commutative-algebra isomorphism induced by a finite reindexing. -/
@[stacks 0GZJ "reindexing isomorphism of exact-power Koszul algebras"]
noncomputable def algebraIso {ι κ : Type u} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    powAlgebra f n ≅ powAlgebra (fun j ↦ f (e.symm j)) n where
  hom := algebraHom f e n
  inv := algebraInv f e n
  hom_inv_id := algebraHom_inv_id f e n
  inv_hom_id := algebraInv_hom_id f e n

/-- The forward component of the algebra reindexing is its explicit commutative-algebra map. -/
@[simp]
theorem algebraIso_hom {ι κ : Type u} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    (algebraIso f e n).hom = algebraHom f e n := by
  rfl

/-- The inverse component of the algebra reindexing is its explicit inverse map. -/
@[simp]
theorem algebraIso_inv {ι κ : Type u} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    (algebraIso f e n).inv = algebraInv f e n := by
  rfl

end Reindex

/-- For `n ≤ m`, multiplication makes `K_n` an explicit `(K_m, K_n)`-bimodule through the
exact-power transition `K_m ⟶ K_n`. -/
@[stacks 0GZJ "powered Koszul transition bimodule"]
noncomputable def powBimodule {ι : Type u} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    Bimod (powAlgebra f m).toMon (powAlgebra f n).toMon :=
  restrictionBimodule (powMapLinear f n m) (powMapLinear_compatible f h)

/-- The carrier of the powered transition bimodule is the target Koszul complex. -/
@[simp]
theorem powBimodule_X {ι : Type u} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    (powBimodule f h).X = powComplex f n := by
  rfl

/-- For `n ≤ m`, the multiplication comparison `K_m ⊗ K_n ⟶ K_n`: first apply the
exact-power transition in the left factor, then multiply in `K_n`. -/
@[stacks 0GZJ "multiplication comparison for powered Koszul algebras"]
noncomputable def powTensorMul {ι : Type u} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    HomologicalComplex.tensorObj (powComplex f m) (powComplex f n) ⟶
      powComplex f n :=
  leftAction (powMapLinear f n m) (powMapLinear_compatible f h)

/-- The powered multiplication comparison is transition in the left factor followed by exterior
multiplication. -/
theorem powTensorMul_eq {ι : Type u} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    powTensorMul f h =
      (powMap f h ⊗ₘ 𝟙 (powComplex f n)) ≫ mulHom (powLinearForm f n) := by
  rfl

/-- The left action of the powered transition bimodule is `powTensorMul`. -/
@[simp]
theorem powBimodule_actLeft {ι : Type u} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    (powBimodule f h).actLeft = powTensorMul f h := by
  dsimp [powBimodule, restrictionBimodule, Mon.Hom.rightExtensionBimod, powTensorMul,
    leftAction]
  rw [← tensorHom_id]
  rfl

/-- The linear form determined by the `(n + 1)`st powers of a finite family. -/
@[stacks 0GZJ "powered Koszul linear forms",
  stacks 0H1E "powered Koszul linear forms"]
abbrev powerLinearForm {ι : Type v} [Finite ι] (f : ι → R) (n : ℕ) :
    (ι → R) →ₗ[R] R :=
  powLinearForm f (n + 1)

/-- Zero-based powered stage `n` is the exact-power linear form at exponent `n + 1`. -/
theorem powerLinearForm_eq_powLinearForm {ι : Type v} [Finite ι] (f : ι → R) (n : ℕ) :
    powerLinearForm f n = powLinearForm f (n + 1) := by
  rfl

/-- The diagonal linear map multiplying coordinate `i` by `f i`; for a finite family it underlies
the adjacent map from the `(n + 2)`nd-power Koszul stage to the `(n + 1)`st-power stage. -/
@[stacks 0GZJ "linear map underlying powered Koszul transitions"]
def powerStepLinearMap {ι : Type v} (f : ι → R) :
    (ι → R) →ₗ[R] (ι → R) :=
  LinearMap.pi fun i ↦ (f i) • LinearMap.proj i

/-- The zero-based adjacent diagonal map is the exact-power transition from exponent `n + 2`
to exponent `n + 1`. -/
theorem powerStepLinearMap_eq_powMapLinear {ι : Type v} (f : ι → R) (n : ℕ) :
    powerStepLinearMap f = powMapLinear f (n + 1) (n + 2) := by
  ext x i
  simp [powerStepLinearMap, powMapLinear]

/-- The diagonal step map intertwines consecutive powered linear forms. -/
@[stacks 0GZJ "compatibility of powered Koszul transitions"]
theorem powerStep_compatible {ι : Type v} [Finite ι] (f : ι → R) (n : ℕ) :
    (powerLinearForm f n).comp (powerStepLinearMap f) =
      powerLinearForm f (n + 1) := by
  rw [powerStepLinearMap_eq_powMapLinear f n]
  exact powMapLinear_compatible f (Nat.le_succ (n + 1))

/-- Zero-based powered stage `n` is the exact-power Koszul complex at exponent `n + 1`. -/
theorem powerComplex_eq_powComplex {ι : Type v} [Finite ι] (f : ι → R) (n : ℕ) :
    powerComplex f n = powComplex f (n + 1) := by
  rfl

/-- A finite-family powered Koszul complex has no homology above the number of its generators. -/
@[stacks 0H1E "finite homology amplitude for powered Koszul complexes"]
theorem powerComplex_homology_isZero_of_card_lt {ι : Type v} [Finite ι] (f : ι → R)
    (n p : ℕ) (hp : Nat.card ι < p) :
    CategoryTheory.Limits.IsZero ((powerComplex f n).homology p) := by
  classical
  letI := Fintype.ofFinite ι
  have hid : (LinearMap.id : ⋀[R]^p (ι → R) →ₗ[R] ⋀[R]^p (ι → R)) = 0 := by
    apply exteriorPower.linearMap_ext
    apply (Pi.basisFun R ι).ext_alternating
    intro v hv
    have hcard : p ≤ Nat.card ι := by
      simpa only [Fintype.card_eq_nat_card, Nat.card_fin] using
        Fintype.card_le_of_injective v hv
    exact (not_le_of_gt hp hcard).elim
  letI : Subsingleton (⋀[R]^p (ι → R)) := by
    have hz (x : ⋀[R]^p (ι → R)) : x = 0 := by
      exact DFunLike.congr_fun hid x
    exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩
  apply CategoryTheory.ShortComplex.isZero_homology_of_isZero_X₂ ((powerComplex f n).sc p)
  change CategoryTheory.Limits.IsZero (ModuleCat.of R (⋀[R]^p (ι → R)))
  exact ModuleCat.isZero_of_subsingleton _

/-- The degree-`k` exterior-power map induced by the adjacent diagonal datum; for a finite family
it underlies the transition from powered stage `n + 1` to powered stage `n`. -/
@[stacks 0GZJ "degreewise powered Koszul transition"]
noncomputable def powerStepComponent {ι : Type v} (f : ι → R) (k : ℕ) :
    (ModuleCat.of R (ι → R)).exteriorPower k ⟶
      (ModuleCat.of R (ι → R)).exteriorPower k :=
  mapComponent (powerStepLinearMap f) k

/-- The component of a zero-based adjacent transition agrees with the corresponding exact-power
component at every zero-based stage. -/
theorem powerStepComponent_eq_powMapComponent {ι : Type v} (f : ι → R)
    (n k : ℕ) :
    powerStepComponent f k = powMapComponent f (n + 1) (n + 2) k := by
  unfold powerStepComponent powMapComponent
  rw [powerStepLinearMap_eq_powMapLinear f n]

/-- The adjacent transition from powered Koszul stage `n + 1` to stage `n`. -/
@[stacks 0GZJ "adjacent transition in the powered Koszul system"]
noncomputable def powerStep {ι : Type v} [Finite ι] (f : ι → R) (n : ℕ) :
    powerComplex f (n + 1) ⟶ powerComplex f n :=
  powMap f (Nat.le_succ (n + 1))

/-- A zero-based adjacent transition is the exact-power transition from exponent `n + 2` to
exponent `n + 1`. -/
theorem powerStep_eq_powMap {ι : Type v} [Finite ι] (f : ι → R) (n : ℕ) :
    powerStep f n = powMap f (Nat.le_succ (n + 1)) := by
  rfl

/-- The degree components of an adjacent powered transition are exterior-power maps induced by
the diagonal step map. -/
@[simp]
theorem powerStep_f {ι : Type v} [Finite ι] (f : ι → R) (n k : ℕ) :
    (powerStep f n).f k = powerStepComponent f k := by
  rw [powerStep_eq_powMap, powMap_f, powerStepComponent_eq_powMapComponent f n k]

/-- The powered Koszul complexes and their adjacent transitions form a sequential inverse
system. -/
@[stacks 0GZJ "powered Koszul inverse system",
  stacks 0H1E "powered Koszul inverse system"]
noncomputable abbrev powerSystem {ι : Type v} [Finite ι] (f : ι → R) :
    ℕᵒᵖ ⥤ ChainComplex (ModuleCat R) ℕ :=
  Functor.ofOpSequence (powerStep f)

/-- The `n`th zero-based powered Koszul stage as a commutative differential graded algebra. -/
@[stacks 0GZJ "zero-based powered Koszul algebra"]
noncomputable abbrev powerAlgebra {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    CommMon (ChainComplex (ModuleCat R) ℕ) :=
  powAlgebra f (n + 1)

/-- The adjacent multiplicative transition from zero-based powered stage `n + 1` to stage
`n`. -/
@[stacks 0GZJ "adjacent multiplicative powered Koszul transition"]
noncomputable def powerAlgebraStep {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    powerAlgebra f (n + 1) ⟶ powerAlgebra f n :=
  powAlgebraMap f (Nat.le_succ (n + 1))

/-- Forgetting multiplication from an adjacent powered-algebra transition gives the adjacent
powered Koszul chain map. -/
@[simp]
theorem powerAlgebraStep_hom {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    (powerAlgebraStep f n).hom.hom = powerStep f n := by
  rfl

/-- The powered Koszul commutative differential graded algebras and their multiplicative
transitions form a sequential inverse system. -/
@[stacks 0GZJ "powered Koszul differential graded algebra inverse system"]
noncomputable abbrev powerAlgebraSystem {ι : Type u} [Finite ι] (f : ι → R) :
    ℕᵒᵖ ⥤ CommMon (ChainComplex (ModuleCat R) ℕ) :=
  Functor.ofOpSequence (powerAlgebraStep f)

/-- The object at index `n` of the powered Koszul algebra system is powered algebra stage
`n`. -/
@[simp]
theorem powerAlgebraSystem_obj {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    (powerAlgebraSystem f).obj (op n) = powerAlgebra f n := by
  rfl

/-- The generating transition of the powered Koszul algebra system is `powerAlgebraStep`. -/
theorem powerAlgebraSystem_map_succ {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    (powerAlgebraSystem f).map (homOfLE (Nat.le_add_right n 1)).op =
      powerAlgebraStep f n := by
  exact Functor.ofOpSequence_map_homOfLE_succ (powerAlgebraStep f) n

/-- For `n ≤ m`, the map from powered Koszul algebra stage `m` to stage `n` is the exact-power
transition from exponent `m + 1` to exponent `n + 1`. -/
@[stacks 0GZJ "arbitrary transition in the powered Koszul algebra system"]
theorem powerAlgebraSystem_map {ι : Type u} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    (powerAlgebraSystem f).map (homOfLE h).op =
      powAlgebraMap f (Nat.add_le_add_right h 1) := by
  induction h with
  | refl =>
    change (powerAlgebraSystem f).map (𝟙 (op n)) = _
    exact (CategoryTheory.Functor.map_id _ _).trans (powAlgebraMap_refl f (n + 1)).symm
  | @step m h ih =>
    have hcomp : (homOfLE (Nat.le_succ m)).op ≫ (homOfLE h).op =
        (homOfLE (Nat.le_trans h (Nat.le_succ m))).op := Subsingleton.elim _ _
    rw [← hcomp, CategoryTheory.Functor.map_comp, powerAlgebraSystem_map_succ, ih]
    exact powAlgebraMap_comp f (Nat.add_le_add_right h 1) (Nat.le_succ (m + 1))

/-- Forgetting multiplication from the powered Koszul algebra system recovers the powered
Koszul chain-complex system. -/
theorem powerAlgebraSystem_comp_forget {ι : Type u} [Finite ι] (f : ι → R) :
    powerAlgebraSystem f ⋙ CommMon.forget (ChainComplex (ModuleCat R) ℕ) =
      powerSystem f := by
  have hmap {n m : ℕ} (h : n ≤ m) :
      ((powerAlgebraSystem f).map (homOfLE h).op).hom.hom =
        (powerSystem f).map (homOfLE h).op := by
    induction h with
    | refl =>
      change ((powerAlgebraSystem f).map (𝟙 (op n))).hom.hom =
        (powerSystem f).map (𝟙 (op n))
      simp only [CategoryTheory.Functor.map_id]
      rfl
    | @step m h ih =>
      have hcomp : (homOfLE (Nat.le_succ m)).op ≫ (homOfLE h).op =
          (homOfLE (Nat.le_trans h (Nat.le_succ m))).op := Subsingleton.elim _ _
      rw [← hcomp, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
      change ((powerAlgebraSystem f).map (homOfLE (Nat.le_succ m)).op).hom.hom ≫
          ((powerAlgebraSystem f).map (homOfLE h).op).hom.hom = _
      rw [powerAlgebraSystem_map_succ, ih]
      change powerStep f m ≫ (powerSystem f).map (homOfLE h).op = _
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      rfl
  refine CategoryTheory.Functor.ext
    (F := powerAlgebraSystem f ⋙ CommMon.forget (ChainComplex (ModuleCat R) ℕ))
    (G := powerSystem f) (fun _ ↦ rfl) ?_
  intro a b g
  simp only [CategoryTheory.Functor.comp_map]
  have hg : g = (homOfLE (leOfHom g.unop)).op := Subsingleton.elim _ _
  rw [hg]
  exact hmap _

/-- The powered Koszul tower as a sequential inverse system of integer-graded cochain
differential graded algebras. -/
@[stacks 0GZJ "powered Koszul cochain-DGA inverse system"]
noncomputable def powerDGASystem {ι : Type u} [Finite ι] (f : ι → R) :
    ℕᵒᵖ ⥤ CochainDGAlgebra R :=
  powerAlgebraSystem f ⋙ CochainDGAlgebra.fromChainCommMon R

/-- The cochain DGA at index `n` is obtained from the `n`th powered Koszul commutative chain
monoid by the canonical chain-to-cochain embedding. -/
@[simp]
theorem powerDGASystem_obj {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    (powerDGASystem f).obj (op n) =
      (CochainDGAlgebra.fromChainCommMon R).obj (powerAlgebra f n) := by
  rfl

/-- The underlying cochain complex at index `n` is the extension by zero of the `n`th powered
Koszul chain complex. -/
@[simp]
theorem powerDGASystem_obj_toCochainComplex
    {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    ((powerDGASystem f).obj (op n)).toCochainComplex =
      (powerComplex f n).extend ComplexShape.embeddingDownNat := by
  rfl

/-- For `n ≤ m`, the powered cochain-DGA transition is the image of the exact-power
multiplicative transition from exponent `m + 1` to exponent `n + 1`. -/
@[stacks 0GZJ "arbitrary transition in the powered Koszul cochain-DGA system"]
theorem powerDGASystem_map {ι : Type u} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    (powerDGASystem f).map (homOfLE h).op =
      (CochainDGAlgebra.fromChainCommMon R).map
        (powAlgebraMap f (Nat.add_le_add_right h 1)) := by
  change (CochainDGAlgebra.fromChainCommMon R).map
    ((powerAlgebraSystem f).map (homOfLE h).op) = _
  rw [powerAlgebraSystem_map]
  rfl

/-- The underlying cochain map of an arbitrary powered DGA transition is extension by zero of
the corresponding exact-power Koszul chain map. -/
@[stacks 0GZJ "underlying map of an arbitrary powered Koszul cochain-DGA transition"]
theorem powerDGASystem_map_toCochainMap
    {ι : Type u} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    ((powerDGASystem f).map (homOfLE h).op).toCochainMap =
      (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat R)).map
        (powMap f (Nat.add_le_add_right h 1)) := by
  rw [powerDGASystem_map]
  rfl

/-- The object at index `n` of the powered Koszul system is powered stage `n`. -/
@[simp]
theorem powerSystem_obj {ι : Type v} [Finite ι] (f : ι → R) (n : ℕ) :
    (powerSystem f).obj (op n) = powerComplex f n := by
  rfl

/-- The generating transition of the powered Koszul system is `powerStep`. -/
theorem powerSystem_map_succ {ι : Type v} [Finite ι] (f : ι → R) (n : ℕ) :
    (powerSystem f).map (homOfLE (Nat.le_add_right n 1)).op = powerStep f n := by
  exact Functor.ofOpSequence_map_homOfLE_succ (powerStep f) n

/-- For `n ≤ m`, the map from powered Koszul stage `m` to stage `n` is the exact-power
transition from exponent `m + 1` to exponent `n + 1`. -/
@[stacks 0GZJ "arbitrary transition in the powered Koszul system"]
theorem powerSystem_map {ι : Type v} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    (powerSystem f).map (homOfLE h).op =
      powMap f (Nat.add_le_add_right h 1) := by
  induction h with
  | refl =>
    change (powerSystem f).map (𝟙 (op n)) = _
    exact (CategoryTheory.Functor.map_id _ _).trans (powMap_refl f (n + 1)).symm
  | @step m h ih =>
    have hcomp : (homOfLE (Nat.le_succ m)).op ≫ (homOfLE h).op =
        (homOfLE (Nat.le_trans h (Nat.le_succ m))).op := Subsingleton.elim _ _
    rw [← hcomp, CategoryTheory.Functor.map_comp, powerSystem_map_succ, ih]
    exact powMap_comp f (Nat.add_le_add_right h 1) (Nat.le_succ (m + 1))

/-- The degree-`k` component of the map from powered Koszul stage `m` to stage `n` is the
exterior-power map induced by the corresponding exact-power diagonal map. -/
@[stacks 0GZJ "degreewise arbitrary transition in the powered Koszul system"]
theorem powerSystem_map_f {ι : Type v} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) (k : ℕ) :
    ((powerSystem f).map (homOfLE h).op).f k =
      powMapComponent f (n + 1) (m + 1) k := by
  rw [powerSystem_map, powMap_f]

/-- The degree-`k` component of a generating transition is the explicit exterior-power map. -/
theorem powerSystem_map_succ_f {ι : Type v} [Finite ι] (f : ι → R) (n k : ℕ) :
    ((powerSystem f).map (homOfLE (Nat.le_add_right n 1)).op).f k =
      powerStepComponent f k := by
  rw [powerSystem_map_succ, powerStep_f]

/-- The generating component of the zero-based powered system in exact-power notation. -/
@[stacks 0GZJ "exact-power form of a powered-system generating component"]
theorem powerSystem_map_succ_f_eq_powMapComponent {ι : Type v} [Finite ι]
    (f : ι → R) (n k : ℕ) :
    ((powerSystem f).map (homOfLE (Nat.le_add_right n 1)).op).f k =
      powMapComponent f (n + 1) (n + 2) k := by
  rw [powerSystem_map_succ_f, powerStepComponent_eq_powMapComponent f n k]

end KoszulComplex
