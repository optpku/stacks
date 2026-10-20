module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import ReasLib.RingTheory.Ideal.Inertia
public import ReasLib.RingTheory.LocalRing.Integral
public import ReasLib.RingTheory.LocalRing.ResidueField.Map
public import ReasLib.RingTheory.Polynomial.Local

/-!
# A mixed-characteristic quadratic extension with inseparable residue field

Adjoining a square root of `t` to `ℤ_[2][t]_{(2)}` gives a quadratic Galois
extension whose wild inertia does not act trivially modulo the square of the
maximal ideal. The sign automorphism displaces the root by twice that root.
-/

@[expose] public section

noncomputable section

open Polynomial Ideal

namespace PadicInt.SqrtT

/-- The discrete valuation ring `A = ℤ_[2][t]_{(2)}`. -/
abbrev base : Type := Polynomial.Local.atMaximal ℤ_[2]

/-- `base` is an integral domain. -/
instance instIsDomain_base : IsDomain base := sorry

/-- `base` is a discrete valuation ring. -/
instance instIsDiscreteValuationRing_base : IsDiscreteValuationRing base := sorry

/-- The residue field of `A` has characteristic `2`. -/
instance instCharP_residue_base : CharP (IsLocalRing.ResidueField base) 2 := sorry

/-- The image of the indeterminate `t` in `A`. -/
def indet : base := algebraMap (Polynomial ℤ_[2]) base X

/-- The monic polynomial `X ^ 2 - t` over `A`. -/
def polynomial : Polynomial base := X ^ 2 - C indet

/-- The quadratic quotient ring `B = A[x] / (x ^ 2 - t)`. -/
abbrev rootRing : Type := AdjoinRoot polynomial

/-- The distinguished root `x` in `B`. -/
def root : rootRing := AdjoinRoot.root polynomial

/-- The distinguished root squares to `t`. -/
theorem root_sq : root ^ 2 = algebraMap base rootRing indet := sorry

/-- The fraction field `K = Frac(A)`. -/
abbrev baseField : Type := FractionRing base

/-- The polynomial `X ^ 2 - t` after base change to `K`. -/
def fractionPolynomial : Polynomial baseField :=
  polynomial.map (algebraMap base baseField)

/-- `X ^ 2 - t` is irreducible over `K`. -/
instance instIrreducible_fractionPolynomial : Fact (Irreducible fractionPolynomial) := sorry

/-- The quadratic extension `L = K(x)` with `x ^ 2 = t`. -/
abbrev rootExtension : Type := AdjoinRoot fractionPolynomial

/-- The distinguished root of `X ^ 2 - t` in `L`. -/
def gen : rootExtension := AdjoinRoot.root fractionPolynomial

/-- The distinguished generator of `L` squares to `t`. -/
theorem gen_sq : gen ^ 2 = algebraMap base rootExtension indet := sorry

/-- The quadratic `L / K` is finite-dimensional. -/
instance instFiniteDimensional : FiniteDimensional baseField rootExtension := sorry

/-- The quadratic `L / K` is Galois. -/
instance instIsGalois : IsGalois baseField rootExtension := sorry

/-- Evaluation of `X ^ 2 - t` at `-x` vanishes in `L`. -/
theorem eval_neg_gen :
    fractionPolynomial.eval₂ (Algebra.ofId baseField rootExtension) (-gen) = 0 := sorry

/-- The `K`-algebra map `L → L` sending the distinguished root to its negative. -/
def galHom : rootExtension →ₐ[baseField] rootExtension :=
  AdjoinRoot.liftAlgHom fractionPolynomial (Algebra.ofId baseField rootExtension) (-gen)
    eval_neg_gen

/-- The involution `galHom` is its own inverse. -/
theorem galHom_comp_self :
    galHom.comp galHom = AlgHom.id baseField rootExtension := sorry

/-- The Galois automorphism `σ` sending `x` to `-x`. -/
def gal : Gal(rootExtension/baseField) :=
  AlgEquiv.ofAlgHom galHom galHom galHom_comp_self galHom_comp_self

/-- `galHom` sends the distinguished root to its negative. -/
theorem galHom_gen : galHom gen = -gen := sorry

/-- The Galois automorphism sends the distinguished root to its negative. -/
theorem gal_gen : gal gen = -gen := sorry

/-- The displacement of the distinguished root under the sign automorphism is `-2 * x`. -/
theorem gal_gen_eq_sub : gal gen = gen - 2 * gen := sorry

/-- The canonical `A`-algebra map from the quadratic quotient ring to `L`. -/
def rootRingMap : rootRing →ₐ[base] rootExtension :=
  AdjoinRoot.mapAlgHom (Algebra.ofId base baseField) polynomial fractionPolynomial dvd_rfl

/-- The canonical `B`-algebra structure on `L` induced by `rootRingMap`. -/
instance instAlgebra_rootRing_rootExtension : Algebra rootRing rootExtension :=
  rootRingMap.toRingHom.toAlgebra

/-- The scalar tower `A → B → L`. -/
instance instIsScalarTower_base_rootRing_rootExtension :
    IsScalarTower base rootRing rootExtension := sorry

/-- The algebra map `B → L` sends the distinguished root of `B` to the generator of `L`. -/
theorem algebraMap_root : algebraMap rootRing rootExtension root = gen := sorry

/-- The distinguished generator of `L` is integral over `A`. -/
theorem isIntegral_gen : IsIntegral base gen := sorry

/-- The distinguished generator of `L` as an element of the integral closure of `A`. -/
def genIntegral : integralClosure base rootExtension := ⟨gen, isIntegral_gen⟩

/-- `genIntegral` is the distinguished generator of `L`. -/
theorem genIntegral_coe : (genIntegral : rootExtension) = gen := sorry

/-- The defining polynomial vanishes at the integral-closure generator. -/
theorem eval_genIntegral :
    polynomial.eval₂ (Algebra.ofId base (integralClosure base rootExtension)) genIntegral = 0 :=
  sorry

/-- Evaluation at the integral generator maps the quadratic quotient to the integral closure. -/
def rootRingToIntegralClosure : rootRing →ₐ[base] integralClosure base rootExtension :=
  AdjoinRoot.liftAlgHom polynomial (Algebra.ofId base (integralClosure base rootExtension))
    genIntegral eval_genIntegral

/-- The comparison map sends the distinguished quotient root to the integral generator. -/
theorem rootRingToIntegralClosure_root :
    rootRingToIntegralClosure root = genIntegral := sorry

/-- The quadratic quotient ring is identified with the integral closure by the comparison map. -/
theorem rootRingToIntegralClosure_bijective :
    Function.Bijective rootRingToIntegralClosure := sorry

/-- The branch `m` obtained by extending the maximal ideal of `A` to the integral closure. -/
def branch : Ideal (integralClosure base rootExtension) :=
  Ideal.map (algebraMap base (integralClosure base rootExtension))
    (IsLocalRing.maximalIdeal base)

/-- The extended maximal ideal is generated by `2` in the integral closure. -/
theorem branch_eq_span_two :
    branch = Ideal.span {(2 : integralClosure base rootExtension)} := sorry

/-- The extended maximal ideal is maximal on the integral closure. -/
instance instIsMaximal_branch : branch.IsMaximal := sorry

/-- The canonical residue-field algebra `κ_A → κ(m)` induced by lying over. -/
instance instResidueAlgebra :
    Algebra (IsLocalRing.maximalIdeal base).ResidueField branch.ResidueField :=
  Ideal.ResidueField.algebraOfLiesOver (IsLocalRing.maximalIdeal base) branch

/-- The residue extension `κ(m) / κ_A` is not separable. -/
theorem not_isSeparable_residue :
    ¬ Algebra.IsSeparable (IsLocalRing.maximalIdeal base).ResidueField branch.ResidueField :=
  sorry

/-- Twice the distinguished quotient root does not lie in the square of the ideal `(2)`. -/
theorem two_mul_root_notMem_sq :
    (2 : rootRing) * root ∉ (Ideal.span {(2 : rootRing)}) ^ 2 := sorry

/-- The sign automorphism negates the distinguished integral-closure generator. -/
theorem gal_smul_genIntegral : gal • genIntegral = -genIntegral := sorry

/-- Twice the integral-closure generator does not lie in the square of the branch ideal. -/
theorem two_mul_genIntegral_notMem_sq :
    (2 : integralClosure base rootExtension) * genIntegral ∉ branch ^ 2 := sorry

/-- The automorphism `σ` lies in wild inertia at `m`. -/
theorem gal_mem_wildInertia :
    gal ∈ branch.wildInertia Gal(rootExtension/baseField) := sorry

/-- The automorphism `σ` does not act as the identity on the integral closure modulo `m ^ 2`. -/
theorem gal_notMem_modSquareInertia :
    gal ∉ branch.modSquareInertia Gal(rootExtension/baseField) := sorry

/-- Mod-square inertia differs from wild inertia in the mixed-characteristic quadratic extension. -/
theorem modSquareInertia_ne_wildInertia :
    branch.modSquareInertia Gal(rootExtension/baseField) ≠
      branch.wildInertia Gal(rootExtension/baseField) := sorry

end PadicInt.SqrtT
