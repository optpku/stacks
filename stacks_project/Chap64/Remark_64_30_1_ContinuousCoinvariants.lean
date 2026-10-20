module

public import ReasLib.RepresentationTheory.Continuous.ResidualHomologyLeft
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.DerivedInvariants
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Trace
public import stacks_project.Chap64.Remark_64_30_1_Extension

/-!
# Source-owned continuous homology for abstract trace formulas

Specialize the actual compact residual construction to the literal kernel of
the supplied degree map. Frobenius is the residual image of hatZOne, rather
than an unsupported equivariant endomorphism of the restricted representation.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
open scoped Ring
noncomputable section
universe u v

namespace ProfiniteGrp.ContinuousTrace

variable (S : DegreeExtension.{u})

/-- The inclusion used in the residual construction has precisely the degree-map kernel. -/
theorem kernel_exact : MonoidHom.range S.inl.toMonoidHom =
    MonoidHom.ker S.deg.hom.toMonoidHom := by
  ext γ
  constructor
  · rintro ⟨g, rfl⟩
    exact g.property
  · intro h
    exact ⟨⟨γ, h⟩, rfl⟩

variable {Λ : Type u} [Ring Λ] [Finite Λ]
variable (M : DiscreteModuleCat Λ S.middle) [Module.Finite Λ M.obj.V]

/-- Actual continuous homology of the original finite left coefficient module. -/
def derivedCoinvariants : DerivedCategory (ModuleCat.{u} Λ) :=
  ResidualHomologyLeft.derived Λ S.G S.middle hatZ S.inl S.deg.hom
    (kernel_exact S) S.deg_surjective M

/-- Frobenius is the quotient action at the canonical degree-one element. -/
def frobeniusEnd : End (derivedCoinvariants S M) :=
  ResidualHomologyLeft.residualEnd Λ S.G S.middle hatZ S.inl S.deg.hom
    (kernel_exact S) S.deg_surjective M hatZOne

/-- Any lift acts through its image in the quotient, not by ordinary G-equivariance. -/
def frobeniusEndWith (γ : S.middle) : End (derivedCoinvariants S M) :=
  ResidualHomologyLeft.residualEnd Λ S.G S.middle hatZ S.inl S.deg.hom
    (kernel_exact S) S.deg_surjective M (S.deg γ)

theorem frobeniusEndWith_eq (γ : S.middle) (hγ : S.deg γ = hatZOne) :
    frobeniusEndWith S M γ = frobeniusEnd S M := by
  unfold frobeniusEndWith frobeniusEnd
  rw [hγ]

/-- The canonical trace API consumes supplied perfectness; this file does not derive it from cd. -/
def traceFrobeniusPow (hperf : DerivedCategory.IsPerfect (derivedCoinvariants S M))
    (n : ℕ) : Λ♮ :=
  hperf.traceNatural (frobeniusEnd S M ^ n)

theorem traceFrobeniusPow_independent
    (hperf : DerivedCategory.IsPerfect (derivedCoinvariants S M))
    (γ γ' : S.middle) (hγ : S.deg γ = hatZOne) (hγ' : S.deg γ' = hatZOne) (n : ℕ) :
    hperf.traceNatural (frobeniusEndWith S M γ ^ n) =
      hperf.traceNatural (frobeniusEndWith S M γ' ^ n) := by
  rw [frobeniusEndWith_eq S M γ hγ, frobeniusEndWith_eq S M γ' hγ']

/-- Continuous cohomological dimension on prime-torsion discrete modules.
The caller restricts ℓ to primes; no assertion about ℓ=0 is encoded. -/
def HasFiniteEllCohomologicalDimension (ℓ : ℕ) (G : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : Prop :=
  ∃ d : ℕ, ∀ (N : DiscreteModuleCat ℤ G) (i : ℕ),
    (∀ x : N.obj.V, ℓ • x = 0) → d < i →
      CategoryTheory.Limits.IsZero ((DiscreteModuleCat.derivedCohomologyFunctor ℤ G i).obj N)

/-- Concrete coefficient endomorphism of an arithmetic group element. -/
def smulEnd {A : Type v} [Ring A] (N : DiscreteModuleCat A S.middle) (γ : S.middle) :
    Module.End A N.obj.V := (N.obj.ρ γ).hom

/-- The conjugacy class of the nth power, using the existing quotient representative. -/
def powClass (c : ConjClasses S.middle) (n : ℕ) : ConjClasses S.middle :=
  ConjClasses.mk (Quotient.out c ^ n)

/-- Noncommutative finite-projective trace on the original coefficient representation. -/
def conjClassTrace {A : Type v} [Ring A] (N : DiscreteModuleCat A S.middle)
    [Module.Finite A N.obj.V] [Module.Projective A N.obj.V] (c : ConjClasses S.middle) : A♮ :=
  LinearMap.FiniteProjective.traceNatural (smulEnd S N (Quotient.out c))

end ProfiniteGrp.ContinuousTrace
