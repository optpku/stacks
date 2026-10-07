module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.FiniteType
public import stacks_project.Chap98.Definition_98_13_1_Versal
public import stacks_project.Chap98.Remark_98_21_8_Canonical_element_Lift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical element of the tangent functor

Under the RS* setup of Lemma 98.21.2, an affine open `Spec(Λ) ⊂ S` with
`Λ ⟶ A` produces the canonical deformation `x_can ∈ T_x(Ω_{A/Λ})`. If
`Λ` is Noetherian and `Λ ⟶ A` is of finite type, functoriality of `T_x`
sends `θ : Hom_A(Ω_{A/Λ}, κ(u0))` to `T_x(θ)(x_can)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- The residue field `κ(u0)` as an `A`-module along a ring map `A ⟶ κ(u0)`. -/
def residueModule {A : CommRingCat.{u}} {k : Type u} [CommRing k]
    (π : A ⟶ CommRingCat.of k) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars π.hom).obj (ModuleCat.of k k)

/-- `residueModule π` is restriction of scalars of `k` along `π`. -/
theorem residueModule_eq {A : CommRingCat.{u}} {k : Type u} [CommRing k]
    (π : A ⟶ CommRingCat.of k) :
    residueModule π = (ModuleCat.restrictScalars π.hom).obj (ModuleCat.of k k) :=
  sorry

variable {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
variable {Λ A : CommRingCat.{u}} (v : Λ ⟶ A)
variable {σΛ : Spec Λ ⟶ S} {σA : Spec A ⟶ S} (hv : Spec.map v ≫ σΛ = σA)
variable (x : X.p.Fiber (Over.mk σA))

/-- Remark 98.21.8 (Canonical element) (1). Assumptions and notation as in
Lemma 98.21.2. Choose an affine open `Spec(Λ) ⊂ S` such that `Spec(A) ⟶ S`
corresponds to a ring map `Λ ⟶ A`. The section `a ↦ (a, d_{A/Λ}(a))` of
`A ⟶ A[Ω_{A/Λ}]` pulls `x` back to a deformation `x_can` of `x` over
`A[Ω_{A/Λ}]`. This is the canonical element
`x_can ∈ T_x(Ω_{A/Λ}) = Lift(x, A[Ω_{A/Λ}])`. -/
@[stacks 07YC]
def canonicalElement_ofAffineOpen (h_open : IsOpenImmersion σΛ) :
    (tangentFunctor x).obj (kaehlerObj v) :=
  canonicalElement v hv x h_open

/-- Source-facing `canonicalElement_ofAffineOpen` is the core `canonicalElement`. -/
theorem canonicalElement_ofAffineOpen_eq (h_open : IsOpenImmersion σΛ) :
    canonicalElement_ofAffineOpen v hv x h_open = canonicalElement v hv x h_open :=
  sorry

/-- Remark 98.21.8 (Canonical element) (2). If `Λ` is Noetherian and `Λ ⟶ A` is
of finite type, and `u0` is a finite type point of `U = Spec(A)` with
`k = κ(u0)` and `x0 = x|_{u0}`, then `Hom_A(Ω_{A/Λ}, k) ≅ Der_Λ(A, k) ≅
Tℱ_{U,k,u0}` (see Formal Deformation Theory, Example 90.11.11). Functoriality
of `T_x` sends `θ` to `T_x(θ)(x_can)` in `T_x(k) = Tℱ_{X,k,x0}`. -/
@[stacks 07YC]
def inducedTangentMap (h_open : IsOpenImmersion σΛ)
    (h_noetherian : IsNoetherianRing Λ) (h_finiteType : v.hom.FiniteType)
    (u0 : Spec A) (h_finiteTypePoint : IsFiniteTypePoint u0)
    (π : A ⟶ CommRingCat.of (residueFieldType u0))
    (hπ : Spec.map π = fromResidueField u0)
    (θ : kaehlerObj v ⟶ residueModule π) :
    (tangentFunctor x).obj (residueModule π) :=
  have := h_noetherian
  have := h_finiteType
  have := h_finiteTypePoint
  have := hπ
  evalCanonical v hv x h_open θ

/-- `inducedTangentMap` is `evalCanonical` at a residue-field module map. -/
theorem inducedTangentMap_apply (h_open : IsOpenImmersion σΛ)
    (h_noetherian : IsNoetherianRing Λ) (h_finiteType : v.hom.FiniteType)
    (u0 : Spec A) (h_finiteTypePoint : IsFiniteTypePoint u0)
    (π : A ⟶ CommRingCat.of (residueFieldType u0))
    (hπ : Spec.map π = fromResidueField u0)
    (θ : kaehlerObj v ⟶ residueModule π) :
    inducedTangentMap v hv x h_open h_noetherian h_finiteType u0 h_finiteTypePoint π hπ θ =
      evalCanonical v hv x h_open θ :=
  sorry

end AlgebraicGeometry.GroupoidsOver
