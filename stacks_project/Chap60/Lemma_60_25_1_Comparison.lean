/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.DeRham.Connection.Scalar
public import ReasLib.RingTheory.Kaehler.DeRham.Connection.BaseChange

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

/-- The degree-indexed additive groups in the tensor de Rham complex with one-form module `Ω'`. -/
def tensorDeRhamTargetTerm
    (B Ω' M : Type u) [CommRing B] [AddCommGroup Ω'] [Module B Ω']
    [AddCommGroup M] [Module B M] : ℕ → AddCommGrpCat.{u}
  | 0 => AddCommGrpCat.of M
  | p + 1 => AddCommGrpCat.of (M ⊗[B] exteriorPower.form B Ω' (p + 1))

/-- The target tensor de Rham complex assembled from its supplied differentials. -/
def tensorDeRhamComplex
    {B Ω' M : Type u} [CommRing B] [AddCommGroup Ω'] [Module B Ω']
    [AddCommGroup M] [Module B M]
    (targetDifferential : (n : ℕ) →
      tensorDeRhamTargetTerm B Ω' M n ⟶ tensorDeRhamTargetTerm B Ω' M (n + 1))
    (targetSquareZero : ∀ n, targetDifferential n ≫ targetDifferential (n + 1) = 0) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  CochainComplex.of (tensorDeRhamTargetTerm B Ω' M) targetDifferential targetSquareZero

/-- Multiplication by `a` on each source tensor de Rham term. -/
def tensorDeRhamScalarComponent
    {A B Ω M : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω] [Module A Ω] [IsScalarTower A B Ω]
    [AddCommGroup M] [Module B M]
    {d : Derivation A B Ω} (connection : Connection d M) (a : B) :
    ∀ n, Connection.deRhamTerm connection n ⟶ Connection.deRhamTerm connection n :=
  Connection.deRhamScalarComponent connection a

/-- The canonical `B`-linear inclusion `Ω → Ω'` reconstructed from the form splitting. -/
noncomputable def canonicalOmegaMap
    {B B' Ω Ω' : Type u} [CommRing B] [CommRing B'] [Algebra B B']
    [AddCommGroup Ω] [Module B Ω]
    [AddCommGroup Ω'] [Module B' Ω'] [Module B Ω'] [IsScalarTower B B' Ω']
    (formDecomp : Ω' ≃ₗ[B'] (B' ⊗[B] Ω) × B') : Ω →ₗ[B] Ω' :=
  (formDecomp.symm.toLinearMap.restrictScalars B).comp
    ((TensorProduct.mk B B' Ω (1 : B')).prod (0 : Ω →ₗ[B] B'))

/-- The degreewise fixed-base tensor comparison induced by the splitting inclusion
`Ω → Ω'`; its exterior powers are taken over `B`. -/
noncomputable def tensorDeRhamComparisonComponent
    {A B B' Ω Ω' M : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [CommRing B'] [Algebra B B']
    [AddCommGroup Ω] [Module B Ω] [Module A Ω] [IsScalarTower A B Ω]
    [AddCommGroup Ω'] [Module B' Ω'] [Module B Ω'] [IsScalarTower B B' Ω']
    [AddCommGroup M] [Module B M]
    {d : Derivation A B Ω} (connection : Connection d M)
    (formDecomp : Ω' ≃ₗ[B'] (B' ⊗[B] Ω) × B') :
    ∀ n, Connection.deRhamTerm connection n ⟶ tensorDeRhamTargetTerm B Ω' M n
  | 0 => AddCommGrpCat.ofHom (AddMonoidHom.id M)
  | p + 1 =>
      AddCommGrpCat.ofHom
        (TensorProduct.map (LinearMap.id : M →ₗ[B] M)
          (exteriorPower.form.map (canonicalOmegaMap formDecomp) (p + 1))).toAddMonoidHom

/-- Multiplication by `a` on the source de Rham complex. -/
noncomputable def tensorDeRhamScalar
    {A B Ω M : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω] [Module A Ω] [IsScalarTower A B Ω]
    [AddCommGroup M] [Module B M]
    {d : Derivation A B Ω} {δ : DifferentialOperator.DeRham.Family A B Ω}
    {calculus : ExteriorCalculus d δ} {connection : Connection d M}
    (h_integrable : Connection.IsIntegrable connection calculus) (a : B)
    (h_da : d a = 0) :
    Connection.deRhamComplex connection calculus h_integrable ⟶
      Connection.deRhamComplex connection calculus h_integrable :=
  Connection.deRhamScalar h_integrable a h_da

/-- Multiplication by `a` on the scalar-extended de Rham complex. -/
noncomputable def tensorDeRhamTargetScalar
    {A B Ω M : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω] [Module A Ω] [IsScalarTower A B Ω]
    [AddCommGroup M] [Module B M]
    {d : Derivation A B Ω} {δ : DifferentialOperator.DeRham.Family A B Ω}
    {calculus : ExteriorCalculus d δ} {connection : Connection d M}
    (h_integrable : Connection.IsIntegrable connection calculus) (a : B)
    (h_da : d a = 0) :
    Connection.deRhamComplex connection calculus h_integrable ⟶
      Connection.deRhamComplex connection calculus h_integrable :=
  Connection.deRhamScalar h_integrable a h_da

/-- The canonical comparison `c_M` after a compatible scalar extension. -/
noncomputable def tensorDeRhamComparison
    {A B B' Ω Ω' M : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [CommRing B'] [Algebra A B'] [Algebra B B'] [IsScalarTower A B B']
    [AddCommGroup Ω] [Module B Ω] [Module A Ω] [IsScalarTower A B Ω]
    [AddCommGroup Ω'] [Module B' Ω'] [Module A Ω'] [IsScalarTower A B' Ω']
    [Module B Ω'] [IsScalarTower B B' Ω']
    [AddCommGroup M] [Module B M]
    {d : Derivation A B Ω} {δ : DifferentialOperator.DeRham.Family A B Ω}
    {d' : Derivation A B' Ω'} {δ' : DifferentialOperator.DeRham.Family A B' Ω'}
    {calculus : ExteriorCalculus d δ} {calculus' : ExteriorCalculus d' δ'}
    {connection : Connection d M}
    (h_integrable : Connection.IsIntegrable connection calculus)
    (φ : Ω →ₗ[B] Ω')
    (h_compatible : Connection.CompatibleCalculi φ calculus calculus')
    (h_integrable' :
      Connection.IsIntegrable
        (Connection.scalarExtension connection φ h_compatible.derivation) calculus') :
    Connection.deRhamComplex connection calculus h_integrable ⟶
      Connection.deRhamComplex
        (Connection.scalarExtension connection φ h_compatible.derivation) calculus' h_integrable' :=
  { f := Connection.baseChangeDeRhamHom_f connection calculus h_integrable
      (Connection.scalarExtension connection φ h_compatible.derivation) calculus' h_integrable' φ
    comm' := fun first second _ ↦
      Connection.baseChangeDeRhamHom_comm connection calculus h_integrable calculus' φ
        h_compatible h_integrable' first second }
