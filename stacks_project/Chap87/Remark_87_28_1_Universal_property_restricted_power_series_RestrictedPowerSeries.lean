/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Defs.Induced

/-!
# Restricted power series

Restricted power series over a linearly topologized ring `A` are realized as the inverse limit
of polynomial rings `A ⧸ I` in the variables `σ`, indexed by open ideals `I` of `A`, and equipped
with the inverse-limit topology.
-/

@[expose] public section

universe u v w

noncomputable section

namespace RestrictedPowerSeries

/-- An open ideal of a topological ring, viewed as an index of the inverse system
`I ↦ (A ⧸ I)[σ]`. -/
abbrev OpenIdeal (A : Type v) [CommRing A] [TopologicalSpace A] :=
  { I : Ideal A // IsOpen (I : Set A) }

/-- The underlying set of an open ideal is open. -/
theorem isOpen_coe {A : Type v} [CommRing A] [TopologicalSpace A] (I : OpenIdeal A) :
    IsOpen (I.1 : Set A) :=
  sorry

/-- A family of polynomial reductions is compatible when it is functorial along
inclusions of open ideals. -/
def Compatible {σ : Type u} {A : Type v} [CommRing A] [TopologicalSpace A]
    (f : ∀ I : OpenIdeal A, MvPolynomial σ (A ⧸ I.1)) : Prop :=
  ∀ (I J : OpenIdeal A) (h : I.1 ≤ J.1),
    MvPolynomial.map (Ideal.Quotient.factor h) (f I) = f J

/-- Unfolding of inverse-system compatibility. -/
theorem compatible_iff {σ : Type u} {A : Type v} [CommRing A] [TopologicalSpace A]
    (f : ∀ I : OpenIdeal A, MvPolynomial σ (A ⧸ I.1)) :
    Compatible f ↔
      ∀ (I J : OpenIdeal A) (h : I.1 ≤ J.1),
        MvPolynomial.map (Ideal.Quotient.factor h) (f I) = f J :=
  sorry

end RestrictedPowerSeries

/-- Restricted power series in the variables `σ` over a linearly topologized ring `A`, as the
inverse limit of the discrete polynomial rings `(A ⧸ I)[σ]` over open ideals `I`. For
`σ = Fin r` this is the ring `A{x₁, …, xᵣ}`. -/
def RestrictedPowerSeries (σ : Type u) (A : Type v)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] :
    Type (max u v) :=
  { f : ∀ I : RestrictedPowerSeries.OpenIdeal A, MvPolynomial σ (A ⧸ I.1) //
    RestrictedPowerSeries.Compatible f }

namespace RestrictedPowerSeries

variable {σ : Type u} {A : Type v}
variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]

/-- Zero restricted power series, componentwise. -/
instance : Zero (RestrictedPowerSeries σ A) where
  zero := ⟨fun _ ↦ 0, sorry⟩

/-- Unit restricted power series, componentwise. -/
instance : One (RestrictedPowerSeries σ A) where
  one := ⟨fun _ ↦ 1, sorry⟩

/-- Pointwise addition of restricted power series. -/
instance : Add (RestrictedPowerSeries σ A) where
  add x y := ⟨fun I ↦ x.1 I + y.1 I, sorry⟩

/-- Pointwise negation of restricted power series. -/
instance : Neg (RestrictedPowerSeries σ A) where
  neg x := ⟨fun I ↦ -x.1 I, sorry⟩

/-- Pointwise subtraction of restricted power series. -/
instance : Sub (RestrictedPowerSeries σ A) where
  sub x y := ⟨fun I ↦ x.1 I - y.1 I, sorry⟩

/-- Pointwise multiplication of restricted power series. -/
instance : Mul (RestrictedPowerSeries σ A) where
  mul x y := ⟨fun I ↦ x.1 I * y.1 I, sorry⟩

/-- Natural-number scalar multiplication of restricted power series. -/
instance : SMul ℕ (RestrictedPowerSeries σ A) where
  smul n x := ⟨fun I ↦ n • x.1 I, sorry⟩

/-- Integer scalar multiplication of restricted power series. -/
instance : SMul ℤ (RestrictedPowerSeries σ A) where
  smul n x := ⟨fun I ↦ n • x.1 I, sorry⟩

/-- Natural-number powers of restricted power series. -/
instance : Pow (RestrictedPowerSeries σ A) ℕ where
  pow x n := ⟨fun I ↦ x.1 I ^ n, sorry⟩

/-- Canonical map from `ℕ` into restricted power series. -/
instance : NatCast (RestrictedPowerSeries σ A) where
  natCast n := ⟨fun _ ↦ n, sorry⟩

/-- Canonical map from `ℤ` into restricted power series. -/
instance : IntCast (RestrictedPowerSeries σ A) where
  intCast n := ⟨fun _ ↦ n, sorry⟩

/-- Restricted power series form a commutative ring, with componentwise operations. -/
instance : CommRing (RestrictedPowerSeries σ A) where
  add := Add.add
  zero := Zero.zero
  neg := Neg.neg
  sub := Sub.sub
  mul := Mul.mul
  one := One.one
  nsmul := SMul.smul
  zsmul := SMul.smul
  npow := fun n x ↦ Pow.pow x n
  natCast := Nat.cast
  intCast := Int.cast
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul_zero := sorry
  nsmul_succ := sorry
  neg_add_cancel := sorry
  add_comm := sorry
  sub_eq_add_neg := sorry
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  npow_zero := sorry
  npow_succ := sorry
  left_distrib := sorry
  right_distrib := sorry
  mul_comm := sorry
  zero_mul := sorry
  mul_zero := sorry
  natCast_zero := sorry
  natCast_succ := sorry
  intCast_ofNat := sorry
  intCast_negSucc := sorry

/-- Coefficient ring acting by constant polynomials in each component. -/
instance : Algebra A (RestrictedPowerSeries σ A) :=
  RingHom.toAlgebra
    { toFun a := ⟨fun I ↦ MvPolynomial.C (Ideal.Quotient.mk I.1 a), sorry⟩
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry }

/-- The canonical `A`-algebra map from the polynomial ring into restricted power series,
reducing coefficients modulo each open ideal. -/
def ofPolynomial : MvPolynomial σ A →ₐ[A] RestrictedPowerSeries σ A where
  toFun p := ⟨fun I ↦ MvPolynomial.map (Ideal.Quotient.mk I.1) p, sorry⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry

/-- Evaluation of a restricted power series at an open ideal, landing in `(A ⧸ I)[σ]`. -/
def component (I : OpenIdeal A) : RestrictedPowerSeries σ A →+* MvPolynomial σ (A ⧸ I.1) where
  toFun f := f.1 I
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- Inverse-limit topology: the infimum of the discrete topologies on the polynomial
components `(A ⧸ I)[σ]`. -/
instance : TopologicalSpace (RestrictedPowerSeries σ A) :=
  ⨅ I : OpenIdeal A,
    TopologicalSpace.induced (fun f : RestrictedPowerSeries σ A ↦ f.1 I)
      (⊥ : TopologicalSpace (MvPolynomial σ (A ⧸ I.1)))

/-- Restricted power series form a topological ring. -/
instance : IsTopologicalRing (RestrictedPowerSeries σ A) :=
  sorry

/-- The inverse-limit topology on restricted power series is linear. -/
instance : IsLinearTopology (RestrictedPowerSeries σ A) (RestrictedPowerSeries σ A) :=
  sorry

/-- Restricted power series are Hausdorff. -/
instance : T2Space (RestrictedPowerSeries σ A) :=
  sorry

/-- Restricted power series are complete for the additive right uniformity. -/
instance instCompleteSpace :
    @CompleteSpace (RestrictedPowerSeries σ A)
      (IsTopologicalAddGroup.rightUniformSpace (RestrictedPowerSeries σ A)) :=
  sorry

/-- Scalar multiplication by coefficients is continuous on restricted power series. -/
instance : ContinuousSMul A (RestrictedPowerSeries σ A) :=
  sorry

/-- Extensionality of restricted power series by their open-ideal components. -/
theorem ext {f g : RestrictedPowerSeries σ A}
    (h : ∀ I : OpenIdeal A, component I f = component I g) : f = g :=
  sorry

/-- Componentwise evaluation of a restricted power series. -/
theorem component_apply (I : OpenIdeal A) (f : RestrictedPowerSeries σ A) :
    component I f = f.1 I :=
  sorry

/-- The canonical polynomial map reduces coefficients modulo each open ideal. -/
theorem ofPolynomial_apply (p : MvPolynomial σ A) (I : OpenIdeal A) :
    component I (ofPolynomial p) = MvPolynomial.map (Ideal.Quotient.mk I.1) p :=
  sorry

/-- Constants are sent to the algebra map of restricted power series. -/
theorem ofPolynomial_C (a : A) :
    ofPolynomial (MvPolynomial.C a) = algebraMap A (RestrictedPowerSeries σ A) a :=
  sorry

/-- Indeterminates remain indeterminates in every polynomial component. -/
theorem ofPolynomial_X (i : σ) (I : OpenIdeal A) :
    component I (ofPolynomial (MvPolynomial.X i)) = MvPolynomial.X i :=
  sorry

end RestrictedPowerSeries
