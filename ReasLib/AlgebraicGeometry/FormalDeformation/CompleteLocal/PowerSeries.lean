/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalHomotopy
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Instances
public import ReasLib.AlgebraicGeometry.FormalDeformation.TypesCompletion
public import ReasLib.RingTheory.LocalRing.IdealQuotient
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Order.Disjoint

/-!
# Power series morphisms in `CompleteLocalAlgCat`

A morphism `f : R ⟶ S` exhibits `S` as a finite-variable power series ring over `R`
when, after an isomorphism of complete local algebras, it becomes the canonical
coefficient inclusion `R.mvPowerSeriesC n`.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- A morphism `f : R ⟶ S` exhibits `S` as a power series ring over `R` if there is
`n : ℕ` and an isomorphism `e : S ≅ R.mvPowerSeries n` with
`f ≫ e.hom = R.mvPowerSeriesC n`. -/
def IsPowerSeriesOver {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S) : Prop :=
  ∃ n : ℕ, ∃ e : S ≅ R.mvPowerSeries n, f ≫ e.hom = R.mvPowerSeriesC n

/-- Being a power series over `R` unpacks to a finite-variable isomorphism over the
canonical coefficient inclusion. -/
theorem isPowerSeriesOver_iff {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S) :
    IsPowerSeriesOver f ↔
      ∃ n : ℕ, ∃ e : S ≅ R.mvPowerSeries n, f ≫ e.hom = R.mvPowerSeriesC n :=
  sorry

/-- An isomorphism onto `R.mvPowerSeries n` over `R.mvPowerSeriesC n` exhibits a
power series morphism. -/
theorem IsPowerSeriesOver.of_iso {R S : CompleteLocalAlgCat Λ k} {n : ℕ} {f : R ⟶ S}
    (e : S ≅ R.mvPowerSeries n) (h : f ≫ e.hom = R.mvPowerSeriesC n) :
    IsPowerSeriesOver f :=
  sorry

/-- The canonical coefficient inclusion `R.mvPowerSeriesC n` is a power series
morphism over `R`. -/
theorem isPowerSeriesOver_mvPowerSeriesC (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    IsPowerSeriesOver (R.mvPowerSeriesC n) :=
  sorry

/-- `I ⧸ m_R I` is a `k`-vector space via the residue identification of `R`. -/
noncomputable instance instModule_idealSmulQuot {R : CompleteLocalAlgCat Λ k}
    {I : Ideal R.carrier} : Module k (idealSmulQuot I) :=
  Module.compHom (idealSmulQuot I) R.residueFieldIso.symm.toRingHom

/-- A power series evaluation over a split complete local algebra is bijective if its
coordinates form a residue-field basis of `I / m_R I` and its sufficiently deep
maximal-adic truncations have left inverses in the Artinian-local category. -/
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
