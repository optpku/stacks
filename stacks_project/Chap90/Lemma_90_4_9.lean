/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.PowerSeries
import StacksCheckRecall

/-!
# Power series evaluation criterion in `Ĉ_Λ`

A characterized `R'`-algebra map `R'[[X₁,…,Xᵣ]] ⟶ R` is an isomorphism when `R = R' ⊕ I`,
the images of the coordinates form a `k`-basis of `I / m_R I`, and the induced truncation maps
have left inverses in `C_Λ` for all sufficiently large `n`.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/- Lemma 90.4.9: if `R', R` are objects of `Ĉ_Λ = CompleteLocalAlgCat Λ k` with
`R = R' ⊕ I` for an ideal `I` of `R`, the images of `x i ∈ I` form a `k`-basis of
`I / m_R I`, and the `R'`-algebra map `φ : R'[[X i]] ⟶ R` sending `X i` to `x i` has a
left inverse in `C_Λ` on `S / m_S^n ⟶ R / m_R^n` for all `n ≫ 0`, then `φ` is an
isomorphism. -/
@[stacks 06SG] #check (CompleteLocalAlgCat.mvPowerSeriesEval_bijective :
  ∀ {R' R : CompleteLocalAlgCat Λ k} (ι : R' ⟶ R)
    (I : Ideal R.carrier)
    (hcompl : IsCompl (LinearMap.range ι.hom.toLinearMap) (I.restrictScalars Λ))
    {r : ℕ} (x : Fin r → I)
    (hind : LinearIndependent k (fun i ↦ idealSmulQuot.mk (x i)))
    (hspan : Submodule.span k (Set.range fun i ↦ idealSmulQuot.mk (x i)) = ⊤)
    (φ : R'.mvPowerSeries r ⟶ R) (hφ_C : R'.mvPowerSeriesC r ≫ φ = ι)
    (hφ_X : ∀ i, φ.hom (MvPowerSeries.X i) = (x i : R.carrier))
    (hleft : ∃ N, ∀ n, N ≤ n →
      ∃ g : R.truncation n ⟶ (R'.mvPowerSeries r).truncation n,
        truncationHom φ n ≫ g = 𝟙 ((R'.mvPowerSeries r).truncation n)),
    Function.Bijective φ.hom)

end CompleteLocalAlgCat
