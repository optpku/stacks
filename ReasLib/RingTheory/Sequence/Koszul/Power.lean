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
    powMapLinear f n m x i = f i ^ (m - n) * x i := sorry

/-- The exact-power diagonal map intertwines the linear forms at exponents `m` and `n`. -/
@[stacks 0GZJ "compatibility of exact-power Koszul transitions"]
theorem powMapLinear_compatible {ι : Type v} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    (powLinearForm f n).comp (powMapLinear f n m) = powLinearForm f m := sorry

/-- The diagonal map at a reflexive exponent inequality is the identity. -/
@[simp]
theorem powMapLinear_refl {ι : Type v} (f : ι → R) (n : ℕ) :
    powMapLinear f n n = LinearMap.id := sorry

/-- Exact-power diagonal maps compose according to transitivity of exponent inequalities. -/
theorem powMapLinear_comp {ι : Type v} (f : ι → R) {n m l : ℕ}
    (h_nm : n ≤ m) (h_ml : m ≤ l) :
    (powMapLinear f n m).comp (powMapLinear f m l) = powMapLinear f n l := sorry

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
    (powMap f h).f k = powMapComponent f n m k := sorry

/-- The exact-power transition associated to reflexivity is the identity chain map. -/
@[simp]
theorem powMap_refl {ι : Type v} [Finite ι] (f : ι → R) (n : ℕ) :
    powMap f (le_refl n) = 𝟙 (powComplex f n) := sorry

/-- Exact-power Koszul transitions compose according to transitivity of exponent inequalities. -/
theorem powMap_comp {ι : Type v} [Finite ι] (f : ι → R) {n m l : ℕ}
    (h_nm : n ≤ m) (h_ml : m ≤ l) :
    powMap f h_ml ≫ powMap f h_nm = powMap f (h_nm.trans h_ml) := sorry

namespace Reindex

/-- Reindexing a finite family transports its exact-power Koszul linear form along
`LinearEquiv.piCongrLeft'`. -/
@[stacks 0GZJ "reindexed exact-power linear-form compatibility"]
theorem powLinearForm_reindex {ι κ : Type v} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    (powLinearForm (fun j ↦ f (e.symm j)) n).comp
        (LinearEquiv.piCongrLeft' R (fun _ : ι ↦ R) e).toLinearMap =
      powLinearForm f n := sorry

/-- The inverse coordinate reindexing transports the target exact-power linear form back. -/
@[stacks 0GZJ "inverse reindexed exact-power linear-form compatibility"]
theorem powLinearForm_reindex_symm {ι κ : Type v} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    (powLinearForm f n).comp
        (LinearEquiv.piCongrLeft' R (fun _ : ι ↦ R) e).symm.toLinearMap =
      powLinearForm (fun j ↦ f (e.symm j)) n := sorry

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
    chainHom f e n ≫ chainInv f e n = 𝟙 (powComplex f n) := sorry

/-- The inverse reindexing map followed by reindexing is the identity on the target complex. -/
theorem chainInv_hom_id {ι κ : Type v} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    chainInv f e n ≫ chainHom f e n =
      𝟙 (powComplex (fun j ↦ f (e.symm j)) n) := sorry

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
    (chainIso f e n).hom = chainHom f e n := sorry

/-- The inverse component of the chain reindexing is its explicit inverse Koszul map. -/
@[simp]
theorem chainIso_inv {ι κ : Type v} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    (chainIso f e n).inv = chainInv f e n := sorry

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
    (powAlgebra f n).X = powComplex f n := sorry

/-- For `n ≤ m`, the exact-power Koszul transition as a morphism of commutative differential
graded algebras. -/
@[stacks 0GZJ "multiplicative exact-power Koszul transition"]
noncomputable def powAlgebraMap {ι : Type u} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    powAlgebra f m ⟶ powAlgebra f n :=
  commMonMap (powMapLinear f n m) (powMapLinear_compatible f h)

/-- The underlying chain map of a multiplicative exact-power transition is `powMap`. -/
@[simp]
theorem powAlgebraMap_hom {ι : Type u} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    (powAlgebraMap f h).hom.hom = powMap f h := sorry

/-- The multiplicative exact-power transition attached to reflexivity is the identity. -/
@[simp]
theorem powAlgebraMap_refl {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    powAlgebraMap f (le_refl n) = 𝟙 (powAlgebra f n) := sorry

/-- Multiplicative exact-power transitions compose according to transitivity. -/
theorem powAlgebraMap_comp {ι : Type u} [Finite ι] (f : ι → R) {n m l : ℕ}
    (h_nm : n ≤ m) (h_ml : m ≤ l) :
    powAlgebraMap f h_ml ≫ powAlgebraMap f h_nm =
      powAlgebraMap f (h_nm.trans h_ml) := sorry

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
    (algebraHom f e n).hom.hom = chainHom f e n := sorry

/-- The underlying chain map of the inverse algebra reindexing is the canonical inverse map. -/
@[simp]
theorem algebraInv_hom {ι κ : Type u} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    (algebraInv f e n).hom.hom = chainInv f e n := sorry

/-- Forward algebra reindexing followed by its inverse is the identity. -/
theorem algebraHom_inv_id {ι κ : Type u} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    algebraHom f e n ≫ algebraInv f e n = 𝟙 (powAlgebra f n) := sorry

/-- Inverse algebra reindexing followed by reindexing is the identity. -/
theorem algebraInv_hom_id {ι κ : Type u} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    algebraInv f e n ≫ algebraHom f e n =
      𝟙 (powAlgebra (fun j ↦ f (e.symm j)) n) := sorry

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
    (algebraIso f e n).hom = algebraHom f e n := sorry

/-- The inverse component of the algebra reindexing is its explicit inverse map. -/
@[simp]
theorem algebraIso_inv {ι κ : Type u} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    (algebraIso f e n).inv = algebraInv f e n := sorry

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
    (powBimodule f h).X = powComplex f n := sorry

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
      (powMap f h ⊗ₘ 𝟙 (powComplex f n)) ≫ mulHom (powLinearForm f n) := sorry

/-- The left action of the powered transition bimodule is `powTensorMul`. -/
@[simp]
theorem powBimodule_actLeft {ι : Type u} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    (powBimodule f h).actLeft = powTensorMul f h := sorry

/-- The linear form determined by the `(n + 1)`st powers of a finite family. -/
@[stacks 0GZJ "powered Koszul linear forms",
  stacks 0H1E "powered Koszul linear forms"]
abbrev powerLinearForm {ι : Type v} [Finite ι] (f : ι → R) (n : ℕ) :
    (ι → R) →ₗ[R] R :=
  powLinearForm f (n + 1)

/-- Zero-based powered stage `n` is the exact-power linear form at exponent `n + 1`. -/
theorem powerLinearForm_eq_powLinearForm {ι : Type v} [Finite ι] (f : ι → R) (n : ℕ) :
    powerLinearForm f n = powLinearForm f (n + 1) := sorry

/-- The diagonal linear map multiplying coordinate `i` by `f i`; for a finite family it underlies
the adjacent map from the `(n + 2)`nd-power Koszul stage to the `(n + 1)`st-power stage. -/
@[stacks 0GZJ "linear map underlying powered Koszul transitions"]
def powerStepLinearMap {ι : Type v} (f : ι → R) :
    (ι → R) →ₗ[R] (ι → R) :=
  LinearMap.pi fun i ↦ (f i) • LinearMap.proj i

/-- The zero-based adjacent diagonal map is the exact-power transition from exponent `n + 2`
to exponent `n + 1`. -/
theorem powerStepLinearMap_eq_powMapLinear {ι : Type v} (f : ι → R) (n : ℕ) :
    powerStepLinearMap f = powMapLinear f (n + 1) (n + 2) := sorry

/-- The diagonal step map intertwines consecutive powered linear forms. -/
@[stacks 0GZJ "compatibility of powered Koszul transitions"]
theorem powerStep_compatible {ι : Type v} [Finite ι] (f : ι → R) (n : ℕ) :
    (powerLinearForm f n).comp (powerStepLinearMap f) =
      powerLinearForm f (n + 1) := sorry

/-- Zero-based powered stage `n` is the exact-power Koszul complex at exponent `n + 1`. -/
theorem powerComplex_eq_powComplex {ι : Type v} [Finite ι] (f : ι → R) (n : ℕ) :
    powerComplex f n = powComplex f (n + 1) := sorry

/-- A finite-family powered Koszul complex has no homology above the number of its generators. -/
@[stacks 0H1E "finite homology amplitude for powered Koszul complexes"]
theorem powerComplex_homology_isZero_of_card_lt {ι : Type v} [Finite ι] (f : ι → R)
    (n p : ℕ) (hp : Nat.card ι < p) :
    CategoryTheory.Limits.IsZero ((powerComplex f n).homology p) := sorry

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
    powerStepComponent f k = powMapComponent f (n + 1) (n + 2) k := sorry

/-- The adjacent transition from powered Koszul stage `n + 1` to stage `n`. -/
@[stacks 0GZJ "adjacent transition in the powered Koszul system"]
noncomputable def powerStep {ι : Type v} [Finite ι] (f : ι → R) (n : ℕ) :
    powerComplex f (n + 1) ⟶ powerComplex f n :=
  powMap f (Nat.le_succ (n + 1))

/-- A zero-based adjacent transition is the exact-power transition from exponent `n + 2` to
exponent `n + 1`. -/
theorem powerStep_eq_powMap {ι : Type v} [Finite ι] (f : ι → R) (n : ℕ) :
    powerStep f n = powMap f (Nat.le_succ (n + 1)) := sorry

/-- The degree components of an adjacent powered transition are exterior-power maps induced by
the diagonal step map. -/
@[simp]
theorem powerStep_f {ι : Type v} [Finite ι] (f : ι → R) (n k : ℕ) :
    (powerStep f n).f k = powerStepComponent f k := sorry

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
    (powerAlgebraStep f n).hom.hom = powerStep f n := sorry

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
    (powerAlgebraSystem f).obj (op n) = powerAlgebra f n := sorry

/-- The generating transition of the powered Koszul algebra system is `powerAlgebraStep`. -/
theorem powerAlgebraSystem_map_succ {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    (powerAlgebraSystem f).map (homOfLE (Nat.le_add_right n 1)).op =
      powerAlgebraStep f n := sorry

/-- For `n ≤ m`, the map from powered Koszul algebra stage `m` to stage `n` is the exact-power
transition from exponent `m + 1` to exponent `n + 1`. -/
@[stacks 0GZJ "arbitrary transition in the powered Koszul algebra system"]
theorem powerAlgebraSystem_map {ι : Type u} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    (powerAlgebraSystem f).map (homOfLE h).op =
      powAlgebraMap f (Nat.add_le_add_right h 1) := sorry

/-- Forgetting multiplication from the powered Koszul algebra system recovers the powered
Koszul chain-complex system. -/
theorem powerAlgebraSystem_comp_forget {ι : Type u} [Finite ι] (f : ι → R) :
    powerAlgebraSystem f ⋙ CommMon.forget (ChainComplex (ModuleCat R) ℕ) =
      powerSystem f := sorry

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
      (CochainDGAlgebra.fromChainCommMon R).obj (powerAlgebra f n) := sorry

/-- The underlying cochain complex at index `n` is the extension by zero of the `n`th powered
Koszul chain complex. -/
@[simp]
theorem powerDGASystem_obj_toCochainComplex
    {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    ((powerDGASystem f).obj (op n)).toCochainComplex =
      (powerComplex f n).extend ComplexShape.embeddingDownNat := sorry

/-- For `n ≤ m`, the powered cochain-DGA transition is the image of the exact-power
multiplicative transition from exponent `m + 1` to exponent `n + 1`. -/
@[stacks 0GZJ "arbitrary transition in the powered Koszul cochain-DGA system"]
theorem powerDGASystem_map {ι : Type u} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    (powerDGASystem f).map (homOfLE h).op =
      (CochainDGAlgebra.fromChainCommMon R).map
        (powAlgebraMap f (Nat.add_le_add_right h 1)) := sorry

/-- The underlying cochain map of an arbitrary powered DGA transition is extension by zero of
the corresponding exact-power Koszul chain map. -/
@[stacks 0GZJ "underlying map of an arbitrary powered Koszul cochain-DGA transition"]
theorem powerDGASystem_map_toCochainMap
    {ι : Type u} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    ((powerDGASystem f).map (homOfLE h).op).toCochainMap =
      (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat R)).map
        (powMap f (Nat.add_le_add_right h 1)) := sorry

/-- The object at index `n` of the powered Koszul system is powered stage `n`. -/
@[simp]
theorem powerSystem_obj {ι : Type v} [Finite ι] (f : ι → R) (n : ℕ) :
    (powerSystem f).obj (op n) = powerComplex f n := sorry

/-- The generating transition of the powered Koszul system is `powerStep`. -/
theorem powerSystem_map_succ {ι : Type v} [Finite ι] (f : ι → R) (n : ℕ) :
    (powerSystem f).map (homOfLE (Nat.le_add_right n 1)).op = powerStep f n := sorry

/-- For `n ≤ m`, the map from powered Koszul stage `m` to stage `n` is the exact-power
transition from exponent `m + 1` to exponent `n + 1`. -/
@[stacks 0GZJ "arbitrary transition in the powered Koszul system"]
theorem powerSystem_map {ι : Type v} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    (powerSystem f).map (homOfLE h).op =
      powMap f (Nat.add_le_add_right h 1) := sorry

/-- The degree-`k` component of the map from powered Koszul stage `m` to stage `n` is the
exterior-power map induced by the corresponding exact-power diagonal map. -/
@[stacks 0GZJ "degreewise arbitrary transition in the powered Koszul system"]
theorem powerSystem_map_f {ι : Type v} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) (k : ℕ) :
    ((powerSystem f).map (homOfLE h).op).f k =
      powMapComponent f (n + 1) (m + 1) k := sorry

/-- The degree-`k` component of a generating transition is the explicit exterior-power map. -/
theorem powerSystem_map_succ_f {ι : Type v} [Finite ι] (f : ι → R) (n k : ℕ) :
    ((powerSystem f).map (homOfLE (Nat.le_add_right n 1)).op).f k =
      powerStepComponent f k := sorry

/-- The generating component of the zero-based powered system in exact-power notation. -/
@[stacks 0GZJ "exact-power form of a powered-system generating component"]
theorem powerSystem_map_succ_f_eq_powMapComponent {ι : Type v} [Finite ι]
    (f : ι → R) (n k : ℕ) :
    ((powerSystem f).map (homOfLE (Nat.le_add_right n 1)).op).f k =
      powMapComponent f (n + 1) (n + 2) k := sorry

end KoszulComplex
