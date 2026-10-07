module

public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Order.Disjoint
public import Mathlib.RingTheory.Ideal.Cotangent
public import stacks_project.Chap90.Lemma_90_28_2_FormalHomotopy
public import stacks_project.Chap90.Remark_90_7_6_TypesCompletion

/-!
# Power series evaluation criterion in `Ĉ_Λ`

A characterized `R'`-algebra map `R'[[X₁,…,Xᵣ]] ⟶ R` is an isomorphism when `R = R' ⊕ I`,
the images of the coordinates form a `k`-basis of `I / m_R I`, and the induced truncation maps
have left inverses in `C_Λ` for all sufficiently large `n`.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The quotient module `I ⧸ m_R I` of an ideal by the action of the maximal ideal. -/
def idealSmulQuot (I : Ideal R) : Type u :=
  I ⧸ (maximalIdeal R • ⊤ : Submodule R I)
deriving AddCommGroup, Module R, Module (R ⧸ maximalIdeal R)

namespace idealSmulQuot

/-- The quotient class of an element of `I` in `I ⧸ m_R I`. -/
def mk {I : Ideal R} : I → idealSmulQuot I :=
  Submodule.Quotient.mk

/-- The class of `x` vanishes if and only if the underlying element of `R` lies in `m_R * I`. -/
theorem mk_eq_zero_iff {I : Ideal R} (x : I) :
    mk x = 0 ↔ (x : R) ∈ maximalIdeal R * I :=
  sorry

/-- `I ⧸ m_R I` is a vector space over the residue field. -/
instance moduleResidueField {I : Ideal R} : Module (ResidueField R) (idealSmulQuot I) :=
  inferInstanceAs <| Module (R ⧸ maximalIdeal R) (I ⧸ (maximalIdeal R • ⊤ : Submodule R I))

end idealSmulQuot

end IsLocalRing

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- `I ⧸ m_R I` is a `k`-vector space via the residue identification of `R`. -/
noncomputable instance instModule_idealSmulQuot {R : CompleteLocalAlgCat Λ k}
    {I : Ideal R.carrier} : Module k (idealSmulQuot I) :=
  Module.compHom (idealSmulQuot I) R.residueFieldIso.symm.toRingHom

/-- Lemma 90.4.9: if `R', R` are objects of `Ĉ_Λ = CompleteLocalAlgCat Λ k` with
`R = R' ⊕ I` for an ideal `I` of `R`, the images of `x i ∈ I` form a `k`-basis of
`I / m_R I`, and the `R'`-algebra map `φ : R'[[X i]] ⟶ R` sending `X i` to `x i` has a
left inverse in `C_Λ` on `S / m_S^n ⟶ R / m_R^n` for all `n ≫ 0`, then `φ` is an
isomorphism. -/
@[stacks 06SG]
theorem mvPowerSeriesEval_bijective {R' R : CompleteLocalAlgCat Λ k} (ι : R' ⟶ R)
    (I : Ideal R.carrier)
    (hcompl : IsCompl (LinearMap.range ι.hom.toLinearMap) (I.restrictScalars Λ))
    {r : ℕ} (x : Fin r → I)
    (hind : LinearIndependent k (fun i ↦ idealSmulQuot.mk (x i)))
    (hspan : Submodule.span k (Set.range fun i ↦ idealSmulQuot.mk (x i)) = ⊤)
    (φ : R'.mvPowerSeries r ⟶ R) (hφ_C : R'.mvPowerSeriesC r ≫ φ = ι)
    (hφ_X : ∀ i, φ.hom (MvPowerSeries.X i) = (x i : R.carrier))
    (hleft : ∃ N, ∀ n, N ≤ n →
      ∃ g : R.truncation n ⟶ (R'.mvPowerSeries r).truncation n,
        truncationHom φ n ≫ g = 𝟙 ((R'.mvPowerSeries r).truncation n)) :
    Function.Bijective φ.hom :=
  sorry

end CompleteLocalAlgCat
