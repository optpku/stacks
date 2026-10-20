/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.InverseLimit
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.InverseLimit
import StacksCheckRecall

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Lemma 90.4.8. A surjective tower with bounded cotangent dimensions has a
complete local inverse limit, and its projection kernels define the maximal-adic topology. -/
@[stacks 06SF] #check (CompleteLocalAlgCat.ofInverseLimit :
  ∀ (A : ℕ → ArtinianLocalAlgCat Λ k) (f : ∀ n, A (n + 1) ⟶ A n)
    (hf : ∀ n, Function.Surjective (f n).hom)
    (hdim : ∃ B : ℕ, ∀ n,
      Module.finrank (ResidueField (A n).carrier) (CotangentSpace (A n).carrier) ≤ B),
    CompleteLocalAlgCat Λ k)

#check (CompleteLocalAlgCat.kerAdicFiltration :
  ∀ (A : ℕ → ArtinianLocalAlgCat Λ k) (f : ∀ n, A (n + 1) ⟶ A n)
    (hf : ∀ n, Function.Surjective (f n).hom)
    (hdim : ∃ B : ℕ, ∀ n,
      Module.finrank (ResidueField (A n).carrier) (CotangentSpace (A n).carrier) ≤ B),
    CompleteLocalAlgCat.AdicIdealFiltration (CompleteLocalAlgCat.ofInverseLimit A f hf hdim))

#check (CompleteLocalAlgCat.ofInverseLimit_carrier :
  ∀ (A : ℕ → ArtinianLocalAlgCat Λ k) (f : ∀ n, A (n + 1) ⟶ A n)
    (hf : ∀ n, Function.Surjective (f n).hom)
    (hdim : ∃ B : ℕ, ∀ n,
      Module.finrank (ResidueField (A n).carrier) (CotangentSpace (A n).carrier) ≤ B),
    (CompleteLocalAlgCat.ofInverseLimit A f hf hdim).carrier =
      ArtinianLocalAlgCat.inverseLimit A f)

#check (CompleteLocalAlgCat.ofInverseLimit_spec :
  ∀ (A : ℕ → ArtinianLocalAlgCat Λ k) (f : ∀ n, A (n + 1) ⟶ A n)
    (hf : ∀ n, Function.Surjective (f n).hom)
    (hdim : ∃ B : ℕ, ∀ n,
      Module.finrank (ResidueField (A n).carrier) (CotangentSpace (A n).carrier) ≤ B),
    IsNoetherianRing (CompleteLocalAlgCat.ofInverseLimit A f hf hdim).carrier ∧
      IsCompleteLocalRing (CompleteLocalAlgCat.ofInverseLimit A f hf hdim).carrier ∧
        (CompleteLocalAlgCat.ofInverseLimit A f hf hdim).residueFieldIso =
          ArtinianLocalAlgCat.inverseLimitResidueFieldIso A f hf)

#check (CompleteLocalAlgCat.kerAdicFiltration_ideal :
  ∀ (A : ℕ → ArtinianLocalAlgCat Λ k) (f : ∀ n, A (n + 1) ⟶ A n)
    (hf : ∀ n, Function.Surjective (f n).hom)
    (hdim : ∃ B : ℕ, ∀ n,
      Module.finrank (ResidueField (A n).carrier) (CotangentSpace (A n).carrier) ≤ B),
    ∀ n : ℕ, (CompleteLocalAlgCat.kerAdicFiltration A f hf hdim).ideal n =
      ArtinianLocalAlgCat.ker A f n)

#check (CompleteLocalAlgCat.kerAdicFiltration_spec :
  ∀ (A : ℕ → ArtinianLocalAlgCat Λ k) (f : ∀ n, A (n + 1) ⟶ A n)
    (hf : ∀ n, Function.Surjective (f n).hom)
    (hdim : ∃ B : ℕ, ∀ n,
      Module.finrank (ResidueField (A n).carrier) (CotangentSpace (A n).carrier) ≤ B),
    Antitone (CompleteLocalAlgCat.kerAdicFiltration A f hf hdim).ideal ∧
      (∀ n, (CompleteLocalAlgCat.kerAdicFiltration A f hf hdim).ideal n ≤
        maximalIdeal (CompleteLocalAlgCat.ofInverseLimit A f hf hdim).carrier) ∧
      (∀ n, ∃ m, (CompleteLocalAlgCat.kerAdicFiltration A f hf hdim).ideal m ≤
        maximalIdeal (CompleteLocalAlgCat.ofInverseLimit A f hf hdim).carrier ^ (n + 1)) ∧
      (∀ n, ∃ m, maximalIdeal (CompleteLocalAlgCat.ofInverseLimit A f hf hdim).carrier ^ (m + 1) ≤
        (CompleteLocalAlgCat.kerAdicFiltration A f hf hdim).ideal n))
