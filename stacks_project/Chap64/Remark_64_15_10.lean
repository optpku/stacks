/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap64.Remark_64_15_10_Coinvariants
public import stacks_project.Chap64.Remark_64_15_10_Comparison
public import stacks_project.Chap64.Remark_64_15_10_Trace
public import stacks_project.Chap64.Remark_64_15_10_Trivial

/-!
# The trivial trace formula for a finite group

Illustration of the formula of Lemma 64.15.9 on a finite resolution of the
trivial `Γ`-module `Λ` by `Λ[Γ]`-modules that are finite projective as
`Λ[G]`-modules. Informal commentary on point counts of `BG` and the pointer
to (64.14.3.1) / §64.30 is not formalized here.
-/

@[expose] public section

open Ring CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidAlgebra Ring
open MonoidAlgebra LinearMap.FiniteProjective

noncomputable section

universe u v w

namespace LinearMap.FiniteProjective

variable {Λ : Type u} {G : Type v} {Γ : Type w}
variable [Ring Λ] [Group G] [Monoid Γ] [Finite G]
variable (S : NatMonoidExtension G Γ)
variable (P : ChainComplex (ModuleCat.{u} (Λ[Γ])) ℕ)
variable [∀ n, Module (Λ[G]) (P.X n)] [∀ n, Module Λ (P.X n)]
variable [∀ n, IsScalarTower Λ (Λ[Γ]) (P.X n)]
variable [∀ n, IsScalarTower Λ (Λ[G]) (P.X n)]
variable [∀ n, IsRestrictionAlongInl Λ S (P.X n)]
variable [∀ n, Module.Finite (Λ[G]) (P.X n)]
variable [∀ n, Module.Projective (Λ[G]) (P.X n)]

/-- Remark 64.15.10 (2). If `P_•` is a finite resolution of the trivial
`Γ`-module `Λ` by `Λ[Γ]`-modules that are finite projective as `Λ[G]`-modules,
then for every `γ` the identity `#Z_γ • Tr_Λ^{Z_γ}(γ, P_•) = 1` holds in `Λ♮`. -/
@[stacks 03UE]
theorem traceGComplex_nsmul (r : ℕ)
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[Γ]))).obj (trivialModule Λ Γ))
    [QuasiIso ε] (hr : ∀ n, r < n → IsZero (P.X n)) (γ : Γ) :
    Nat.card (S.centralizer γ) • traceGComplex S P r γ =
      CommutatorQuotient.mk (1 : Λ) :=
  sorry

/-- If `#Z_γ` is invertible in `Λ`, the `Z_γ`-trace of `γ` on the resolution is
the class of `⅟(#Z_γ)`. -/
theorem traceGComplex_eq_inv (r : ℕ)
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[Γ]))).obj (trivialModule Λ Γ))
    [QuasiIso ε] (hr : ∀ n, r < n → IsZero (P.X n)) (γ : Γ)
    [Invertible (Nat.card (S.centralizer γ) : Λ)] :
    traceGComplex S P r γ =
      CommutatorQuotient.mk (⅟(Nat.card (S.centralizer γ) : Λ)) :=
  sorry

/-- Lemma 64.15.9 in alternating form: the identity trace of `1` on `(P_•)_G`
equals the sum of class traces over `G`-conjugacy classes of degree-1
elements. -/
theorem trace_oneEndComplex_eq_sum_conjClassTrace (r : ℕ) :
    trace_oneEndComplex S P r =
      ∑ᶠ c : S.DegreeOneGConjClass, conjClassTraceComplex S P r c :=
  sorry

/-- On each `G`-conjugacy class of a degree-1 element, the alternating class
trace of a finite resolution of the trivial module satisfies
`#Z_γ • Tr_Λ^{Z_γ}(γ, P_•) = 1` in `Λ♮`. -/
theorem conjClassTraceComplex_nsmul (r : ℕ)
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[Γ]))).obj (trivialModule Λ Γ))
    [QuasiIso ε] (hr : ∀ n, r < n → IsZero (P.X n))
    (c : S.DegreeOneGConjClass) :
    S.cardCentralizer c • conjClassTraceComplex S P r c =
      CommutatorQuotient.mk (1 : Λ) :=
  sorry

/-- Remark 64.15.10 (3). If the trivial `Γ`-module `Λ` admits a finite
resolution `P_•` by `Λ[Γ]`-modules that are finite projective as `Λ[G]`-modules
and each `#Z_γ` is a unit in `Λ`, then
`Tr_Λ(1, (P_•)_G) = Tr(1 | H_*(G, Λ)) = ∑'_{γ ↦ 1} ⅟(#Z_γ)` in `Λ♮`.
The middle term is the alternating oneEnd-trace of `(P_•)_G` after transport
along `coinvariantsComplex_homology`. -/
@[stacks 03UE]
theorem trace_oneEndComplex_eq_sum_inv_cardCentralizer (r : ℕ)
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[Γ]))).obj (trivialModule Λ Γ))
    [QuasiIso ε] (hr : ∀ n, r < n → IsZero (P.X n))
    (hc : ∀ c : S.DegreeOneGConjClass, IsUnit (S.cardCentralizer c : Λ)) :
    trace_oneEndComplex S P r =
      ∑ᶠ c : S.DegreeOneGConjClass,
        CommutatorQuotient.mk ((hc c).invertible.invOf : Λ) :=
  sorry

end LinearMap.FiniteProjective

namespace LinearMap.FiniteProjective

variable {Λ G Γ : Type u}
variable [CommRing Λ] [Group G] [Monoid Γ] [Finite G]
variable (S : NatMonoidExtension G Γ)
variable (P : ChainComplex (ModuleCat.{u} (Λ[Γ])) ℕ)
variable [∀ n, Module (Λ[G]) (P.X n)] [∀ n, Module Λ (P.X n)]
variable [∀ n, IsScalarTower Λ (Λ[Γ]) (P.X n)]
variable [∀ n, IsScalarTower Λ (Λ[G]) (P.X n)]
variable [∀ n, IsRestrictionAlongInl Λ S (P.X n)]
variable [∀ n, Module.Finite (Λ[G]) (P.X n)]
variable [∀ n, Module.Projective (Λ[G]) (P.X n)]

/-- Remark 64.15.10 (1). If the trivial `Γ`-module `Λ` admits a finite resolution
`P_•` by `Λ[Γ]`-modules that are finite projective as `Λ[G]`-modules, then
`H_n((P_•)_G) ≅ H_n(G, Λ)`. -/
@[stacks 03UE]
noncomputable def coinvariantsComplex_homology (r : ℕ)
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[Γ]))).obj (trivialModule Λ Γ))
    [QuasiIso ε] (hr : ∀ n, r < n → IsZero (P.X n)) (n : ℕ) :
    (Coinvariants.complex S P).homology n ≅
      groupHomology (Rep.trivial Λ G Λ) n :=
  homologyIso S P ε n

/-- The homology of `(P_•)_G` is identified with `Tor_n^{Λ[G]}(Λ, Λ)`. -/
noncomputable def coinvariantsComplex_homology_iso_tor (r : ℕ)
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[Γ]))).obj (trivialModule Λ Γ))
    [QuasiIso ε] (hr : ∀ n, r < n → IsZero (P.X n)) (n : ℕ) :
    (Coinvariants.complex S P).homology n ≅
      ((Rep.Tor Λ G n).obj (Rep.trivial Λ G Λ)).obj (Rep.trivial Λ G Λ) :=
  homologyIso_tor S P ε n

/-- The identity trace `Tr(1 | H_*(G, Λ))` is the alternating oneEnd-trace of
`(P_•)_G` after transport along `coinvariantsComplex_homology`. If `#G` is a
unit then positive homology vanishes and `H_0 ≅ Λ`, so this equals the class
of `1`. -/
theorem trace_oneEndComplex_eq_homology (r : ℕ)
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[Γ]))).obj (trivialModule Λ Γ))
    [QuasiIso ε] (hr : ∀ n, r < n → IsZero (P.X n))
    (hG : IsUnit (Nat.card G : Λ)) :
    trace_oneEndComplex S P r = CommutatorQuotient.mk (1 : Λ) :=
  sorry

end LinearMap.FiniteProjective

namespace LinearMap.FiniteProjective

variable {Λ G : Type u} [CommRing Λ] [Group G] [Finite G]

/-- If `#G` is a unit in the commutative coefficient ring `Λ`, then `H_n(G, Λ)`
vanishes for all `n > 0`. -/
theorem groupHomology_trivial_isZero_succ (hG : IsUnit (Nat.card G : Λ)) (n : ℕ) :
    IsZero (groupHomology (Rep.trivial Λ G Λ) (n + 1)) :=
  sorry

/-- For trivial coefficients, `H_0(G, Λ) ≅ Λ`. -/
noncomputable def groupHomology_trivial_zero_iso :
    groupHomology (Rep.trivial Λ G Λ) 0 ≅ ModuleCat.of Λ Λ :=
  groupHomology.H0IsoOfIsTrivial (Rep.trivial Λ G Λ)

/-- The inverse of `groupHomology_trivial_zero_iso` is the canonical map from
coefficients to `H_0`. -/
theorem groupHomology_trivial_zero_iso_inv :
    (groupHomology_trivial_zero_iso).inv =
      groupHomology.H0π (Rep.trivial Λ G Λ) :=
  sorry

end LinearMap.FiniteProjective

namespace LinearMap.FiniteProjective

variable {Λ G Γ : Type u} [Field Λ] [Group G] [Monoid Γ] [Finite G]
variable (S : NatMonoidExtension G Γ)

/-- Remark 64.15.10 (4). If `Λ` is a field in which `#G` is invertible, the
trivial trace formula reads `1 = ∑ᶠ 1 / #Z_γ` over `G`-conjugacy classes of
degree-1 elements of `Γ`. This is the source's `F_ℓ` identity when
`Λ = ZMod ℓ` with `ℓ` prime to `#G`. -/
@[stacks 03UE]
theorem one_eq_sum_inv_cardCentralizer (hG : IsUnit (Nat.card G : Λ)) :
    (1 : Λ) = ∑ᶠ c : S.DegreeOneGConjClass, (S.cardCentralizer c : Λ)⁻¹ :=
  sorry

/-- The counting identity of Remark 64.15.10 (4) in `ZMod ℓ` when `ℓ` is prime
to `#G`. -/
theorem one_eq_sum_inv_cardCentralizer_zmod {ℓ : ℕ} [Fact ℓ.Prime]
    (hG : IsUnit (Nat.card G : ZMod ℓ)) :
    (1 : ZMod ℓ) = ∑ᶠ c : S.DegreeOneGConjClass, (S.cardCentralizer c : ZMod ℓ)⁻¹ :=
  sorry

end LinearMap.FiniteProjective
