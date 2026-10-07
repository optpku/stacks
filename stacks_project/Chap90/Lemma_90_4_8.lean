module

public import Mathlib.RingTheory.Ideal.Cotangent
public import stacks_project.Chap90.Definition_90_7_3_CompleteLocal
public import stacks_project.Chap90.Lemma_90_4_8_InverseLimit
public import stacks_project.Chap90.Lemma_90_7_4_Filtration

/-!
# Inverse limits of surjective towers in `C_Λ`

A surjective sequence in `ArtinianLocalAlgCat` with bounded cotangent rank has
inverse limit an object of `CompleteLocalAlgCat`, and the kernels of the
projections define the maximal-adic topology.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

variable (A : ℕ → ArtinianLocalAlgCat Λ k) (f : ∀ n, A (n + 1) ⟶ A n)

/-- Lemma 90.4.8 (1): if `A (n + 1) ⟶ A n` is a sequence of surjective maps in
`ArtinianLocalAlgCat Λ k` and `Module.finrank` of `CotangentSpace (A n).carrier` is
bounded, then `ArtinianLocalAlgCat.inverseLimit A f` is an object of
`CompleteLocalAlgCat Λ k`. -/
@[stacks 06SF]
noncomputable def ofInverseLimit
    (hf : ∀ n, Function.Surjective (f n).hom)
    (hdim : ∃ B : ℕ, ∀ n,
      Module.finrank (ResidueField (A n).carrier) (CotangentSpace (A n).carrier) ≤ B) :
    CompleteLocalAlgCat Λ k where
  carrier := ArtinianLocalAlgCat.inverseLimit A f
  commRing := ArtinianLocalAlgCat.instCommRing_inverseLimit A f
  algebra := ArtinianLocalAlgCat.instAlgebra_inverseLimit A f
  isLocalRing := inferInstance
  isNoetherianRing := sorry
  isCompleteLocalRing := sorry
  residueFieldIso := ArtinianLocalAlgCat.inverseLimitResidueFieldIso A f

/-- The carrier of `ofInverseLimit` is the inverse-limit ring of the tower. -/
theorem ofInverseLimit_carrier
    (hf : ∀ n, Function.Surjective (f n).hom)
    (hdim : ∃ B : ℕ, ∀ n,
      Module.finrank (ResidueField (A n).carrier) (CotangentSpace (A n).carrier) ≤ B) :
    (ofInverseLimit A f hf hdim).carrier = ArtinianLocalAlgCat.inverseLimit A f := sorry

/-- `ofInverseLimit` is Noetherian and complete, with the canonical residue identification. -/
theorem ofInverseLimit_spec
    (hf : ∀ n, Function.Surjective (f n).hom)
    (hdim : ∃ B : ℕ, ∀ n,
      Module.finrank (ResidueField (A n).carrier) (CotangentSpace (A n).carrier) ≤ B) :
    IsNoetherianRing (ofInverseLimit A f hf hdim).carrier ∧
      IsCompleteLocalRing (ofInverseLimit A f hf hdim).carrier ∧
        (ofInverseLimit A f hf hdim).residueFieldIso =
          ArtinianLocalAlgCat.inverseLimitResidueFieldIso A f := sorry

/-- Lemma 90.4.8 (2): the ideals `Ker(S ⟶ A n)` define the `maximalIdeal S`-adic
topology on the inverse limit `S`. -/
@[stacks 06SF]
noncomputable def kerAdicFiltration
    (hf : ∀ n, Function.Surjective (f n).hom)
    (hdim : ∃ B : ℕ, ∀ n,
      Module.finrank (ResidueField (A n).carrier) (CotangentSpace (A n).carrier) ≤ B) :
    AdicIdealFiltration (ofInverseLimit A f hf hdim) :=
  AdicIdealFiltration.of (ArtinianLocalAlgCat.ker A f) sorry sorry sorry sorry

/-- The underlying ideals of `kerAdicFiltration` are the kernels of the projections. -/
theorem kerAdicFiltration_ideal
    (hf : ∀ n, Function.Surjective (f n).hom)
    (hdim : ∃ B : ℕ, ∀ n,
      Module.finrank (ResidueField (A n).carrier) (CotangentSpace (A n).carrier) ≤ B)
    (n : ℕ) :
    (kerAdicFiltration A f hf hdim).ideal n = ArtinianLocalAlgCat.ker A f n := sorry

/-- `kerAdicFiltration` is antitone, contained in the maximal ideal, and cofinal with
the maximal-adic powers in both directions. -/
theorem kerAdicFiltration_spec
    (hf : ∀ n, Function.Surjective (f n).hom)
    (hdim : ∃ B : ℕ, ∀ n,
      Module.finrank (ResidueField (A n).carrier) (CotangentSpace (A n).carrier) ≤ B) :
    Antitone (kerAdicFiltration A f hf hdim).ideal ∧
      (∀ n, (kerAdicFiltration A f hf hdim).ideal n ≤
        maximalIdeal (ofInverseLimit A f hf hdim).carrier) ∧
      (∀ n, ∃ m, (kerAdicFiltration A f hf hdim).ideal m ≤
        maximalIdeal (ofInverseLimit A f hf hdim).carrier ^ (n + 1)) ∧
      (∀ n, ∃ m, maximalIdeal (ofInverseLimit A f hf hdim).carrier ^ (m + 1) ≤
        (kerAdicFiltration A f hf hdim).ideal n) := sorry

end CompleteLocalAlgCat
