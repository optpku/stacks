/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.DeRham.Descent
public import ReasLib.LinearAlgebra.ExteriorPower.Forms
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.Derivation.Basic

@[expose] public section

open scoped TensorProduct
open CategoryTheory

universe u v

/-- A graded exterior-form calculus records the one-form wedge operations and the
graded Leibniz identities needed to extend a connection to all exterior powers.
The explicit wedge data is used because the current exterior-power API does not
bundle these operations. -/
structure ExteriorCalculus
    {A : Type u} [CommRing A]
    {B : Type v} [CommRing B] [Algebra A B]
    {Ω : Type v} [AddCommGroup Ω] [Module B Ω] [Module A Ω]
    [IsScalarTower A B Ω]
    (D : Derivation A B Ω)
    (δ : DifferentialOperator.DeRham.Family A B Ω) where
  /-- Wedge on the left by a one-form. -/
  leftWedge (p : ℕ) : Ω →ₗ[B]
    exteriorPower.form B Ω p →ₗ[B] exteriorPower.form B Ω (p + 1)
  /-- Wedge on the left by a two-form. -/
  leftWedgeTwo (p : ℕ) : exteriorPower.form B Ω 2 →ₗ[B]
    exteriorPower.form B Ω p →ₗ[B] exteriorPower.form B Ω (p + 2)
  /-- The differential obeys the scalar Leibniz rule. -/
  differential_smul (p : ℕ) (b : B) (ω : exteriorPower.form B Ω p) :
    δ p (b • ω) = leftWedge p (D b) ω + b • δ p ω
  /-- The differential obeys the graded Leibniz rule for a one-form on the left. -/
  differential_leftWedge (p : ℕ) (η : Ω) (ω : exteriorPower.form B Ω p) :
    δ (p + 1) (leftWedge p η ω) =
      leftWedgeTwo p (δ 1 η) ω - leftWedge (p + 1) η (δ p ω)
  /-- Successive one-form wedges associate with the two-form wedge. -/
  leftWedge_assoc (p : ℕ) (η ξ : Ω) (ω : exteriorPower.form B Ω p) :
    leftWedge (p + 1) η (leftWedge p ξ ω) =
      leftWedgeTwo p (leftWedge 1 η ξ) ω
  /-- The supplied family is a de Rham differential for `D`. -/
  isDifferential : DifferentialOperator.DeRham.IsDifferential D δ

namespace ExteriorCalculus

variable {A : Type u} [CommRing A]
variable {B : Type v} [CommRing B] [Algebra A B]
variable {Ω : Type v} [AddCommGroup Ω] [Module B Ω] [Module A Ω]
  [IsScalarTower A B Ω]
variable {D : Derivation A B Ω}
variable {δ : DifferentialOperator.DeRham.Family A B Ω}

/-- Construct an exterior calculus from explicit wedge data and its Leibniz laws. -/
def of
    (leftWedge : ∀ p : ℕ, Ω →ₗ[B]
      exteriorPower.form B Ω p →ₗ[B] exteriorPower.form B Ω (p + 1))
    (leftWedgeTwo : ∀ p : ℕ, exteriorPower.form B Ω 2 →ₗ[B]
      exteriorPower.form B Ω p →ₗ[B] exteriorPower.form B Ω (p + 2))
    (differential_smul : ∀ (p : ℕ) (b : B) (ω : exteriorPower.form B Ω p),
      δ p (b • ω) = leftWedge p (D b) ω + b • δ p ω)
    (differential_leftWedge : ∀ (p : ℕ) (η : Ω) (ω : exteriorPower.form B Ω p),
      δ (p + 1) (leftWedge p η ω) =
        leftWedgeTwo p (δ 1 η) ω - leftWedge (p + 1) η (δ p ω))
    (leftWedge_assoc : ∀ (p : ℕ) (η ξ : Ω) (ω : exteriorPower.form B Ω p),
      leftWedge (p + 1) η (leftWedge p ξ ω) =
        leftWedgeTwo p (leftWedge 1 η ξ) ω)
    (isDifferential : DifferentialOperator.DeRham.IsDifferential D δ) :
    ExteriorCalculus D δ :=
  { leftWedge := leftWedge
    leftWedgeTwo := leftWedgeTwo
    differential_smul := differential_smul
    differential_leftWedge := differential_leftWedge
    leftWedge_assoc := leftWedge_assoc
    isDifferential := isDifferential }

/-- The constructor `ExteriorCalculus.of` retains the supplied one-form wedge maps. -/
theorem of_leftWedge
    (leftWedge : ∀ p : ℕ, Ω →ₗ[B]
      exteriorPower.form B Ω p →ₗ[B] exteriorPower.form B Ω (p + 1))
    (leftWedgeTwo : ∀ p : ℕ, exteriorPower.form B Ω 2 →ₗ[B]
      exteriorPower.form B Ω p →ₗ[B] exteriorPower.form B Ω (p + 2))
    (differential_smul : ∀ (p : ℕ) (b : B) (ω : exteriorPower.form B Ω p),
      δ p (b • ω) = leftWedge p (D b) ω + b • δ p ω)
    (differential_leftWedge : ∀ (p : ℕ) (η : Ω) (ω : exteriorPower.form B Ω p),
      δ (p + 1) (leftWedge p η ω) =
        leftWedgeTwo p (δ 1 η) ω - leftWedge (p + 1) η (δ p ω))
    (leftWedge_assoc : ∀ (p : ℕ) (η ξ : Ω) (ω : exteriorPower.form B Ω p),
      leftWedge (p + 1) η (leftWedge p ξ ω) =
        leftWedgeTwo p (leftWedge 1 η ξ) ω)
    (isDifferential : DifferentialOperator.DeRham.IsDifferential D δ) (p : ℕ) :
    (of leftWedge leftWedgeTwo differential_smul differential_leftWedge
      leftWedge_assoc isDifferential).leftWedge p = leftWedge p := rfl

/-- The scalar Leibniz law exposed from an exterior calculus. -/
theorem differential_smul_apply (C : ExteriorCalculus D δ) (p : ℕ) (b : B)
    (ω : exteriorPower.form B Ω p) :
    δ p (b • ω) = C.leftWedge p (D b) ω + b • δ p ω :=
  C.differential_smul p b ω

end ExteriorCalculus

namespace KaehlerDifferential.DeRham

variable {A : Type u} [CommRing A]
variable {B : Type v} [CommRing B] [Algebra A B]
variable {Ω : Type v} [AddCommGroup Ω] [Module B Ω] [Module A Ω]
  [IsScalarTower A B Ω]

/-- The explicit de Rham family descended to a quotient of Kähler differentials. -/
noncomputable def descendedFamily
    (π : Ω[B⁄A] →ₗ[B] Ω) (hπ : Function.Surjective π)
    (δ : DifferentialOperator.DeRham.Family A B Ω[B⁄A])
    (hδ : DifferentialOperator.DeRham.IsDifferential (KaehlerDifferential.D A B) δ)
    (hcondition : DifferentialOperator.DeRham.KernelCondition π δ) :
    DifferentialOperator.DeRham.Family A B Ω :=
  DifferentialOperator.DeRham.Family.descend π
    (fun p ↦ exteriorPower.form.mapRestrictScalars_surjective A π hπ p) δ
    (DifferentialOperator.DeRham.KernelCondition.preservesKernel π hπ δ hδ.formula
      (KaehlerDifferential.span_range_derivation A B) hcondition)

/-- The explicit quotient family satisfies the de Rham differential conditions. -/
theorem descendedFamily_isDifferential
    (π : Ω[B⁄A] →ₗ[B] Ω) (hπ : Function.Surjective π)
    (δ : DifferentialOperator.DeRham.Family A B Ω[B⁄A])
    (hδ : DifferentialOperator.DeRham.IsDifferential (KaehlerDifferential.D A B) δ)
    (hcondition : DifferentialOperator.DeRham.KernelCondition π δ) :
    DifferentialOperator.DeRham.IsDifferential
      (π.compDer (KaehlerDifferential.D A B))
      (descendedFamily π hπ δ hδ hcondition) := by
  exact DifferentialOperator.DeRham.Family.descend_isDifferential π
    (fun p ↦ exteriorPower.form.mapRestrictScalars_surjective A π hπ p) δ hδ
    (DifferentialOperator.DeRham.KernelCondition.preservesKernel π hπ δ hδ.formula
      (KaehlerDifferential.span_range_derivation A B) hcondition)

/-- The explicit quotient family is intertwined with the source family in every degree. -/
theorem descendedFamily_descends
    (π : Ω[B⁄A] →ₗ[B] Ω) (hπ : Function.Surjective π)
    (δ : DifferentialOperator.DeRham.Family A B Ω[B⁄A])
    (hδ : DifferentialOperator.DeRham.IsDifferential (KaehlerDifferential.D A B) δ)
    (hcondition : DifferentialOperator.DeRham.KernelCondition π δ) :
    DifferentialOperator.DeRham.Descends π δ
      (descendedFamily π hπ δ hδ hcondition) := by
  intro p
  -- Pin the four scalar actions used by the degreewise descent construction.
  letI : Module A (exteriorPower.form B Ω[B⁄A] p) :=
    exteriorPower.form.moduleOfScalarTower p
  letI : Module A (exteriorPower.form B Ω[B⁄A] (p + 1)) :=
    exteriorPower.form.moduleOfScalarTower (p + 1)
  letI : Module A (exteriorPower.form B Ω p) :=
    exteriorPower.form.moduleOfScalarTower p
  letI : Module A (exteriorPower.form B Ω (p + 1)) :=
    exteriorPower.form.moduleOfScalarTower (p + 1)
  apply LinearMap.descendOfSurjective_comp

end KaehlerDifferential.DeRham

/-- A connection on a `B`-module with values in a module of one-forms. -/
structure Connection
    {A : Type u} [CommRing A]
    {B : Type v} [CommRing B] [Algebra A B]
    {Ω : Type v} [AddCommGroup Ω] [Module B Ω] [Module A Ω]
    [IsScalarTower A B Ω]
    (D : Derivation A B Ω)
    (M : Type v) [AddCommGroup M] [Module B M] where
  /-- The additive connection map `M → M ⊗[B] Ω`. -/
  toAddMonoidHom : M →+ M ⊗[B] Ω
  /-- The Leibniz rule for scalar multiplication. -/
  leibniz (b : B) (m : M) :
    toAddMonoidHom (b • m) = b • toAddMonoidHom m + m ⊗ₜ[B] D b

namespace Connection

variable {A : Type u} [CommRing A]
variable {B : Type v} [CommRing B] [Algebra A B]
variable {Ω : Type v} [AddCommGroup Ω] [Module B Ω] [Module A Ω]
  [IsScalarTower A B Ω]
variable {D : Derivation A B Ω}
variable {M : Type v} [AddCommGroup M] [Module B M]

/-- Construct a connection from an additive map and a proof of its Leibniz rule. -/
def of (toAddMonoidHom : M →+ M ⊗[B] Ω)
    (leibniz : ∀ (b : B) (m : M),
      toAddMonoidHom (b • m) = b • toAddMonoidHom m + m ⊗ₜ[B] D b) :
    Connection D M :=
  { toAddMonoidHom := toAddMonoidHom
    leibniz := leibniz }

/-- Evaluating a connection built by `Connection.of` recovers its supplied additive map. -/
theorem of_apply (toAddMonoidHom : M →+ M ⊗[B] Ω)
    (leibniz : ∀ (b : B) (m : M),
      toAddMonoidHom (b • m) = b • toAddMonoidHom m + m ⊗ₜ[B] D b)
    (m : M) :
    (of toAddMonoidHom leibniz).toAddMonoidHom m = toAddMonoidHom m := rfl

/-- Evaluate a connection on a module element. -/
def apply (conn : Connection D M) : M → M ⊗[B] Ω :=
  conn.toAddMonoidHom

/-- The connection map satisfies the Leibniz rule. -/
theorem apply_leibniz (conn : Connection D M) (b : B) (m : M) :
    apply conn (b • m) = b • apply conn m + m ⊗ₜ[B] D b :=
  conn.leibniz b m

variable {δ : DifferentialOperator.DeRham.Family A B Ω}

/-- The additive pairing whose tensor lift is the degree-`p` connection differential. -/
def pairing (conn : Connection D M) (C : ExteriorCalculus D δ) (p : ℕ) :
    M →+ exteriorPower.form B Ω p →+
      M ⊗[B] exteriorPower.form B Ω (p + 1) where
  toFun m :=
    { toFun := fun ω ↦
        TensorProduct.map (LinearMap.id : M →ₗ[B] M) ((C.leftWedge p).flip ω)
            (apply conn m) +
          m ⊗ₜ[B] δ p ω
      map_zero' := by simp
      map_add' := by
        intro ω ξ
        simp [TensorProduct.map_add_right, TensorProduct.tmul_add, add_add_add_comm] }
  map_zero' := by
    apply AddMonoidHom.ext
    intro ω
    simp [apply]
  map_add' := by
    intro m n
    apply AddMonoidHom.ext
    intro ω
    simp [apply, TensorProduct.add_tmul, add_add_add_comm]

/-- The pairing is balanced over `B`, so it descends through the tensor product. -/
theorem pairing_balanced (conn : Connection D M) (C : ExteriorCalculus D δ) (p : ℕ)
    (b : B) (m : M) (ω : exteriorPower.form B Ω p) :
    pairing conn C p (b • m) ω = pairing conn C p m (b • ω) := by
  change TensorProduct.map (LinearMap.id : M →ₗ[B] M) ((C.leftWedge p).flip ω)
        (apply conn (b • m)) + (b • m) ⊗ₜ[B] δ p ω =
    TensorProduct.map (LinearMap.id : M →ₗ[B] M) ((C.leftWedge p).flip (b • ω))
        (apply conn m) + m ⊗ₜ[B] δ p (b • ω)
  rw [apply_leibniz, C.differential_smul, map_smul, TensorProduct.map_smul_right]
  simp [TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.smul_tmul,
    add_assoc, add_left_comm]

/-- The degree-`p` extension of a connection to tensor products with `p`-forms. -/
def differential (conn : Connection D M) (C : ExteriorCalculus D δ) (p : ℕ) :
    M ⊗[B] exteriorPower.form B Ω p →+
      M ⊗[B] exteriorPower.form B Ω (p + 1) :=
  TensorProduct.liftAddHom (pairing conn C p) (pairing_balanced conn C p)

/-- On pure tensors, the extended differential is the displayed connection formula. -/
theorem differential_tmul (conn : Connection D M) (C : ExteriorCalculus D δ) (p : ℕ)
    (m : M) (ω : exteriorPower.form B Ω p) :
    differential conn C p (m ⊗ₜ[B] ω) =
      TensorProduct.map (LinearMap.id : M →ₗ[B] M) ((C.leftWedge p).flip ω)
          (apply conn m) +
        m ⊗ₜ[B] δ p ω := rfl

/-- A connection is integrable when the connection map followed by the differential on
one-forms is zero. -/
def IsIntegrable (conn : Connection D M) (C : ExteriorCalculus D δ) : Prop :=
  (differential conn C 1).comp conn.toAddMonoidHom = 0

/-- The square-zero condition for the connection differentials in positive form degree. -/
def SquaresToZero (conn : Connection D M) (C : ExteriorCalculus D δ) : Prop :=
  ∀ p : ℕ,
    (differential conn C (p + 2)).comp (differential conn C (p + 1)) = 0

/-- Integrability is exactly vanishing of the source connection-curvature composite. -/
theorem isIntegrable_iff (conn : Connection D M) (C : ExteriorCalculus D δ) :
    IsIntegrable conn C ↔
      (differential conn C 1).comp conn.toAddMonoidHom = 0 := Iff.rfl

/-- An integrable connection has square-zero differentials in every positive form degree. -/
theorem squaresToZero_of_isIntegrable (conn : Connection D M) (C : ExteriorCalculus D δ)
    (hconn : IsIntegrable conn C) : SquaresToZero conn C := by
  -- Fix the degree-one domain as `M ⊗[B] Ω` before tensor induction.
  let d₁ : M ⊗[B] Ω →+ M ⊗[B] exteriorPower.form B Ω 2 := differential conn C 1
  have d₁_tmul (m : M) (η : Ω) :
      d₁ (m ⊗ₜ[B] η) =
        TensorProduct.map (LinearMap.id : M →ₗ[B] M) ((C.leftWedge 1).flip η)
            (apply conn m) + m ⊗ₜ[B] δ 1 η := rfl
  have differential_wedge (p : ℕ) (ω : exteriorPower.form B Ω p) (x : M ⊗[B] Ω) :
      differential conn C (p + 1)
          (TensorProduct.map (LinearMap.id : M →ₗ[B] M) ((C.leftWedge p).flip ω) x) =
        TensorProduct.map (LinearMap.id : M →ₗ[B] M) ((C.leftWedgeTwo p).flip ω)
            (d₁ x) -
          TensorProduct.map (LinearMap.id : M →ₗ[B] M)
            ((C.leftWedge (p + 1)).flip (δ p ω)) x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m η =>
      have hassoc :
          TensorProduct.map (LinearMap.id : M →ₗ[B] M)
              ((C.leftWedge (p + 1)).flip (C.leftWedge p η ω)) (apply conn m) =
            TensorProduct.map (LinearMap.id : M →ₗ[B] M) ((C.leftWedgeTwo p).flip ω)
              (TensorProduct.map (LinearMap.id : M →ₗ[B] M)
                ((C.leftWedge 1).flip η) (apply conn m)) := by
        induction (apply conn m) using TensorProduct.induction_on with
        | zero => simp
        | tmul n ξ => simp [C.leftWedge_assoc]
        | add x y hx hy => simp [map_add, hx, hy]
      rw [d₁_tmul]
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.flip_apply,
        differential_tmul, C.differential_leftWedge, TensorProduct.tmul_sub, map_add]
      rw [hassoc]
      abel
    | add x y hx hy => simp [map_add, hx, hy, sub_add_sub_comm]
  intro p
  apply AddMonoidHom.ext
  intro x
  change differential conn C (p + 2) (differential conn C (p + 1) x) = 0
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m ω =>
    have hcurv : d₁ (conn.toAddMonoidHom m) = 0 :=
      DFunLike.congr_fun hconn m
    have hδ : δ (p + 2) (δ (p + 1) ω) = 0 := by
      -- Pin the source and target actions of the square-zero linear-map identity.
      letI : Module A (exteriorPower.form B Ω (p + 1)) :=
        exteriorPower.form.moduleOfScalarTower (p + 1)
      letI : Module A (exteriorPower.form B Ω (p + 3)) :=
        exteriorPower.form.moduleOfScalarTower (p + 3)
      exact LinearMap.congr_fun (C.isDifferential.square_zero (p + 1)) ω
    rw [differential_tmul, map_add, differential_wedge, differential_tmul]
    simp [apply, hcurv, hδ]
  | add x y hx hy => simp [map_add, hx, hy]

/-- The degree-indexed additive-group terms of the de Rham complex of a connection. -/
def deRhamTerm (conn : Connection D M) : ℕ → AddCommGrpCat
  | 0 => AddCommGrpCat.of M
  | p + 1 => AddCommGrpCat.of (M ⊗[B] exteriorPower.form B Ω (p + 1))

/-- The degree-raising additive-group morphisms associated to a connection and exterior calculus. -/
def deRhamDifferential (conn : Connection D M) (C : ExteriorCalculus D δ) :
    (n : ℕ) → deRhamTerm conn n ⟶ deRhamTerm conn (n + 1)
  | 0 => AddCommGrpCat.ofHom conn.toAddMonoidHom
  | p + 1 => AddCommGrpCat.ofHom (differential conn C (p + 1))

/-- Consecutive de Rham differentials compose to zero in every degree for an integrable connection. -/
theorem deRhamDifferential_comp (conn : Connection D M) (C : ExteriorCalculus D δ)
    (hconn : IsIntegrable conn C) (n : ℕ) :
    deRhamDifferential conn C n ≫ deRhamDifferential conn C (n + 1) = 0 := by
  apply AddCommGrpCat.hom_ext
  cases n with
  | zero => exact hconn
  | succ p => exact squaresToZero_of_isIntegrable conn C hconn p

/-- The de Rham cochain complex associated to an integrable connection. -/
def deRhamComplex (conn : Connection D M) (C : ExteriorCalculus D δ)
    (hconn : IsIntegrable conn C) : CochainComplex AddCommGrpCat ℕ :=
  CochainComplex.of (deRhamTerm conn) (deRhamDifferential conn C)
    (deRhamDifferential_comp conn C hconn)

/-- The degree-zero term of the de Rham complex is the connection module. -/
theorem deRhamTerm_zero (conn : Connection D M) :
    deRhamTerm conn 0 = AddCommGrpCat.of M := rfl

/-- The successor terms of the de Rham complex are tensor products with exterior forms. -/
theorem deRhamTerm_succ (conn : Connection D M) (p : ℕ) :
    deRhamTerm conn (p + 1) =
      AddCommGrpCat.of (M ⊗[B] exteriorPower.form B Ω (p + 1)) := rfl

/-- The degree-zero de Rham differential is the original additive connection map. -/
theorem deRhamDifferential_zero (conn : Connection D M) (C : ExteriorCalculus D δ) :
    deRhamDifferential conn C 0 = AddCommGrpCat.ofHom conn.toAddMonoidHom := rfl

/-- The successor de Rham differential is the extended connection differential. -/
theorem deRhamDifferential_succ (conn : Connection D M) (C : ExteriorCalculus D δ) (p : ℕ) :
    deRhamDifferential conn C (p + 1) =
      AddCommGrpCat.ofHom (differential conn C (p + 1)) := rfl

/-- The degree-zero object of the concrete de Rham complex. -/
theorem deRhamComplex_X_zero (conn : Connection D M) (C : ExteriorCalculus D δ)
    (hconn : IsIntegrable conn C) :
    (deRhamComplex conn C hconn).X 0 = AddCommGrpCat.of M := rfl

/-- The successor objects of the concrete de Rham complex are tensor products with exterior forms. -/
theorem deRhamComplex_X_succ (conn : Connection D M) (C : ExteriorCalculus D δ)
    (hconn : IsIntegrable conn C) (p : ℕ) :
    (deRhamComplex conn C hconn).X (p + 1) =
      AddCommGrpCat.of (M ⊗[B] exteriorPower.form B Ω (p + 1)) := rfl

/-- The first differential of the concrete de Rham complex is the connection map. -/
theorem deRhamComplex_d_zero (conn : Connection D M) (C : ExteriorCalculus D δ)
    (hconn : IsIntegrable conn C) :
    (deRhamComplex conn C hconn).d 0 1 = AddCommGrpCat.ofHom conn.toAddMonoidHom := by
  exact CochainComplex.of_d (deRhamTerm conn) (deRhamDifferential conn C) 0

/-- The successor differentials of the concrete de Rham complex are the extended connection maps. -/
theorem deRhamComplex_d_succ (conn : Connection D M) (C : ExteriorCalculus D δ)
    (hconn : IsIntegrable conn C) (p : ℕ) :
    (deRhamComplex conn C hconn).d (p + 1) (p + 2) =
      AddCommGrpCat.ofHom (differential conn C (p + 1)) := by
  exact CochainComplex.of_d (deRhamTerm conn) (deRhamDifferential conn C) (p + 1)

end Connection

namespace KaehlerDifferential.DeRham

/-- A connection for a surjective quotient of Kähler differentials is integrable
if its induced de Rham differential has vanishing degree-zero curvature. -/
theorem integrableConnection_squaresToZero
    {A : Type u} [CommRing A]
    {B : Type v} [CommRing B] [Algebra A B]
    {Ω : Type v} [AddCommGroup Ω] [Module B Ω] [Module A Ω]
    [IsScalarTower A B Ω]
    {M : Type v} [AddCommGroup M] [Module B M]
    (π : Ω[B⁄A] →ₗ[B] Ω) (hπ : Function.Surjective π)
    (δ : DifferentialOperator.DeRham.Family A B Ω[B⁄A])
    (hδ : DifferentialOperator.DeRham.IsDifferential (KaehlerDifferential.D A B) δ)
    (hcondition : DifferentialOperator.DeRham.KernelCondition π δ)
    (C : ExteriorCalculus (π.compDer (KaehlerDifferential.D A B))
      (descendedFamily π hπ δ hδ hcondition))
    (conn : Connection (π.compDer (KaehlerDifferential.D A B)) M)
    (hconn : Connection.IsIntegrable conn C) :
    Connection.SquaresToZero conn C :=
  Connection.squaresToZero_of_isIntegrable conn C hconn

end KaehlerDifferential.DeRham
