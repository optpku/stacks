/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap111.Exercise_111_37_6_DegreeMulHom
public import stacks_project.Chap27.Lemma_27_11_8_Veronese
public import ReasLib.RingTheory.MvPolynomial.StandardGrading
import StacksCheckRecall

/-!
# Exercise 111.37.6: maps of `Proj`

A ring map `ψ : R → S` of `ℕ`-graded rings with `ψ(R_d) ⊆ S_{d e}` for `e ≥ 1`
induces a scheme morphism from the open `U = ⋃ D₊(ψ(f)) ⊆ Proj S` to `Proj R`.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open MvPolynomial

noncomputable section

universe u

namespace AlgebraicGeometry

/-
Exercise 111.37.6 (1): a point `p` of `Proj ℬ` lies in the induced open
`DegreeMulHom.domain ψ` if and only if some positive-degree homogeneous `f ∈ 𝒜 d`
satisfies `ψ.toRingHom f ∉ p.asHomogeneousIdeal`.
-/
@[stacks 02A2] #check DegreeMulHom.mem_domain_iff

/-- The substitution `Fin 1 → Fin 2` preserves the standard polynomial grading. -/
theorem coordinateRename_map_mem {d : ℕ} {x : MvPolynomial (Fin 1) ℤ}
    (hx : x ∈ standardGrading (Fin 1) ℤ d) :
    (rename (Fin.castSucc : Fin 1 → Fin 2)).toRingHom x ∈
      standardGrading (Fin 2) ℤ (d * 1) := sorry

/-- The graded substitution of `ℤ[X]` into `ℤ[X, Y]` as a degree-preserving ring map. -/
def coordinateRename :
    DegreeMulHom (standardGrading (Fin 1) ℤ) (standardGrading (Fin 2) ℤ) 1 :=
  DegreeMulHom.ofRingHom
    (rename (Fin.castSucc : Fin 1 → Fin 2)).toRingHom
    (Nat.le_refl 1) coordinateRename_map_mem

/-- Exercise 111.37.6 (2): the open induced by renaming `ℤ[X]` into `ℤ[X, Y]` is not
all of `Proj` of the two-variable ring. -/
@[stacks 02A2]
theorem coordinateRename_domain_ne_top :
    DegreeMulHom.domain coordinateRename ≠ ⊤ := sorry

/-- The identity on `ℤ[X, Y]` preserves the standard polynomial grading. -/
theorem idTwoVars_map_mem {d : ℕ} {x : MvPolynomial (Fin 2) ℤ}
    (hx : x ∈ standardGrading (Fin 2) ℤ d) :
    RingHom.id (MvPolynomial (Fin 2) ℤ) x ∈ standardGrading (Fin 2) ℤ (d * 1) := sorry

/-- The identity of the standard-graded two-variable polynomial ring. -/
def idTwoVars :
    DegreeMulHom (standardGrading (Fin 2) ℤ) (standardGrading (Fin 2) ℤ) 1 :=
  DegreeMulHom.ofRingHom (RingHom.id _) (Nat.le_refl 1) idTwoVars_map_mem

/-- Exercise 111.37.6 (3): the identity on the standard-graded two-variable polynomial
ring induces the full projective spectrum as domain. -/
@[stacks 02A2]
theorem idTwoVars_domain_eq_top :
    DegreeMulHom.domain idTwoVars = ⊤ := sorry

/-
Exercise 111.37.6 (4): the glued scheme morphism `DegreeMulHom.map ψ` is a morphism
of schemes `(DegreeMulHom.domain ψ).toScheme ⟶ Proj 𝒜`.
-/
@[stacks 02A2] #check DegreeMulHom.map

section veroneseInclusion

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The Veronese inclusion preserves the internal Veronese grading. -/
theorem ofInclusion_map_mem (e : ℕ) (he : 1 ≤ e) {n : ℕ}
    {x : GradedRing.Veronese 𝒜 e}
    (hx : x ∈ GradedRing.Veronese.grading 𝒜 e n) :
    GradedRing.Veronese.inclusion 𝒜 e x ∈ 𝒜 (n * e) := sorry

/-- The inclusion of the `e`-Veronese subring of a graded ring as a degree-`e`
homomorphism. -/
def DegreeMulHom.ofInclusion (e : ℕ) (he : 1 ≤ e) :
    DegreeMulHom (GradedRing.Veronese.grading 𝒜 e) 𝒜 e :=
  DegreeMulHom.ofRingHom (GradedRing.Veronese.inclusion 𝒜 e) he
    (ofInclusion_map_mem 𝒜 e he)

/-- The Veronese inclusion induces the full projective spectrum as domain. -/
theorem ofInclusion_domain_eq_top (e : ℕ) (he : 1 ≤ e) :
    DegreeMulHom.domain (DegreeMulHom.ofInclusion 𝒜 e he) = ⊤ := sorry

/-- Exercise 111.37.6 (5): if `R` is the `e`-Veronese subring of `S` and `ψ` is the
inclusion, then the induced morphism is an isomorphism. -/
@[stacks 02A2]
theorem ofInclusion_isIso (e : ℕ) (he : 1 ≤ e) :
    IsIso (DegreeMulHom.mapOnTarget (DegreeMulHom.ofInclusion 𝒜 e he)
        (ofInclusion_domain_eq_top 𝒜 e he)) := sorry

end veroneseInclusion

end AlgebraicGeometry
