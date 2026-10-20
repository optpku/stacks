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
      leftWedge_assoc isDifferential).leftWedge p = leftWedge p := sorry

/-- The scalar Leibniz law exposed from an exterior calculus. -/
theorem differential_smul_apply (C : ExteriorCalculus D δ) (p : ℕ) (b : B)
    (ω : exteriorPower.form B Ω p) :
    δ p (b • ω) = C.leftWedge p (D b) ω + b • δ p ω := sorry

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
      (descendedFamily π hπ δ hδ hcondition) := sorry

/-- The explicit quotient family is intertwined with the source family in every degree. -/
theorem descendedFamily_descends
    (π : Ω[B⁄A] →ₗ[B] Ω) (hπ : Function.Surjective π)
    (δ : DifferentialOperator.DeRham.Family A B Ω[B⁄A])
    (hδ : DifferentialOperator.DeRham.IsDifferential (KaehlerDifferential.D A B) δ)
    (hcondition : DifferentialOperator.DeRham.KernelCondition π δ) :
    DifferentialOperator.DeRham.Descends π δ
      (descendedFamily π hπ δ hδ hcondition) := sorry

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
    (of toAddMonoidHom leibniz).toAddMonoidHom m = toAddMonoidHom m := sorry

/-- Evaluate a connection on a module element. -/
def apply (conn : Connection D M) : M → M ⊗[B] Ω :=
  conn.toAddMonoidHom

/-- The connection map satisfies the Leibniz rule. -/
theorem apply_leibniz (conn : Connection D M) (b : B) (m : M) :
    apply conn (b • m) = b • apply conn m + m ⊗ₜ[B] D b := sorry

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
      map_zero' := sorry
      map_add' := sorry }
  map_zero' := sorry
  map_add' := sorry

/-- The pairing is balanced over `B`, so it descends through the tensor product. -/
theorem pairing_balanced (conn : Connection D M) (C : ExteriorCalculus D δ) (p : ℕ)
    (b : B) (m : M) (ω : exteriorPower.form B Ω p) :
    pairing conn C p (b • m) ω = pairing conn C p m (b • ω) := sorry

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
        m ⊗ₜ[B] δ p ω := sorry

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
      (differential conn C 1).comp conn.toAddMonoidHom = 0 := sorry

/-- An integrable connection has square-zero differentials in every positive form degree. -/
theorem squaresToZero_of_isIntegrable (conn : Connection D M) (C : ExteriorCalculus D δ)
    (hconn : IsIntegrable conn C) : SquaresToZero conn C := sorry

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
    deRhamDifferential conn C n ≫ deRhamDifferential conn C (n + 1) = 0 := sorry

/-- The de Rham cochain complex associated to an integrable connection. -/
def deRhamComplex (conn : Connection D M) (C : ExteriorCalculus D δ)
    (hconn : IsIntegrable conn C) : CochainComplex AddCommGrpCat ℕ :=
  CochainComplex.of (deRhamTerm conn) (deRhamDifferential conn C)
    (deRhamDifferential_comp conn C hconn)

/-- The degree-zero term of the de Rham complex is the connection module. -/
theorem deRhamTerm_zero (conn : Connection D M) :
    deRhamTerm conn 0 = AddCommGrpCat.of M := sorry

/-- The successor terms of the de Rham complex are tensor products with exterior forms. -/
theorem deRhamTerm_succ (conn : Connection D M) (p : ℕ) :
    deRhamTerm conn (p + 1) =
      AddCommGrpCat.of (M ⊗[B] exteriorPower.form B Ω (p + 1)) := sorry

/-- The degree-zero de Rham differential is the original additive connection map. -/
theorem deRhamDifferential_zero (conn : Connection D M) (C : ExteriorCalculus D δ) :
    deRhamDifferential conn C 0 = AddCommGrpCat.ofHom conn.toAddMonoidHom := sorry

/-- The successor de Rham differential is the extended connection differential. -/
theorem deRhamDifferential_succ (conn : Connection D M) (C : ExteriorCalculus D δ) (p : ℕ) :
    deRhamDifferential conn C (p + 1) =
      AddCommGrpCat.ofHom (differential conn C (p + 1)) := sorry

/-- The degree-zero object of the concrete de Rham complex. -/
theorem deRhamComplex_X_zero (conn : Connection D M) (C : ExteriorCalculus D δ)
    (hconn : IsIntegrable conn C) :
    (deRhamComplex conn C hconn).X 0 = AddCommGrpCat.of M := sorry

/-- The successor objects of the concrete de Rham complex are tensor products with exterior forms. -/
theorem deRhamComplex_X_succ (conn : Connection D M) (C : ExteriorCalculus D δ)
    (hconn : IsIntegrable conn C) (p : ℕ) :
    (deRhamComplex conn C hconn).X (p + 1) =
      AddCommGrpCat.of (M ⊗[B] exteriorPower.form B Ω (p + 1)) := sorry

/-- The first differential of the concrete de Rham complex is the connection map. -/
theorem deRhamComplex_d_zero (conn : Connection D M) (C : ExteriorCalculus D δ)
    (hconn : IsIntegrable conn C) :
    (deRhamComplex conn C hconn).d 0 1 = AddCommGrpCat.ofHom conn.toAddMonoidHom := sorry

/-- The successor differentials of the concrete de Rham complex are the extended connection maps. -/
theorem deRhamComplex_d_succ (conn : Connection D M) (C : ExteriorCalculus D δ)
    (hconn : IsIntegrable conn C) (p : ℕ) :
    (deRhamComplex conn C hconn).d (p + 1) (p + 2) =
      AddCommGrpCat.ofHom (differential conn C (p + 1)) := sorry

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
    Connection.SquaresToZero conn C := sorry

end KaehlerDifferential.DeRham
