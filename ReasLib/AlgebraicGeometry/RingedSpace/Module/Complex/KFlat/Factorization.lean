module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Flat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.KFlat.Factorization
import Mathlib.Tactic.CrossRefAttribute

/-!
# K-flat homotopy factorization on ringed spaces

This leaf specializes the ringed-site factorization interface to `𝒪_X`-module complexes.  The
intermediate complex and both comparison maps remain explicit, while termwise flatness is exposed
through the canonical `IsTermwiseFlat` predicate and its ringed-space bridge.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory HomologicalComplex
open SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.CochainComplex

variable {X : RingedSpace.{u}}

/-- Lemma 20.26.17 (0G6V): a morphism from a K-flat complex factors up to homotopy through a
quasi-isomorphism whose source is K-flat. -/
@[stacks 0G6V "ringed-space K-flat homotopy factorization"]
theorem exists_homotopy_factorization_through_kFlat_quasiIso
    (K L : CochainComplex (Modules X) ℤ) (a : K ⟶ L) (hK : K.IsKFlat) :
    ∃ (N : CochainComplex (Modules X) ℤ) (b : K ⟶ N) (c : N ⟶ L),
      Nonempty (Homotopy a (b ≫ c)) ∧ N.IsKFlat ∧ QuasiIso c := sorry

/-- The termwise-flat refinement of the ringed-space K-flat homotopy factorization. -/
@[stacks 0G6V "termwise-flat ringed-space K-flat homotopy factorization"]
theorem exists_termwiseFlat_homotopy_factorization_through_kFlat_quasiIso
    (K L : CochainComplex (Modules X) ℤ) (a : K ⟶ L) (hK : K.IsKFlat)
    (hFlatK : HomologicalComplex.IsTermwiseFlat K) :
    ∃ (N : CochainComplex (Modules X) ℤ) (b : K ⟶ N) (c : N ⟶ L),
      Nonempty (Homotopy a (b ≫ c)) ∧
      N.IsKFlat ∧
      HomologicalComplex.IsTermwiseFlat N ∧
      QuasiIso c := sorry

/-- The source-facing degreewise-flat refinement of the ringed-space factorization. -/
@[stacks 0G6V "degreewise-flat ringed-space K-flat homotopy factorization"]
theorem exists_homotopy_factorization_through_kFlat_quasiIso_of_termwiseFlat
    (K L : CochainComplex (Modules X) ℤ) (a : K ⟶ L) (hK : K.IsKFlat)
    (hFlatK : ∀ n : ℤ, SheafOfModules.IsFlat (K.X n)) :
    ∃ (N : CochainComplex (Modules X) ℤ) (b : K ⟶ N) (c : N ⟶ L),
      Nonempty (Homotopy a (b ≫ c)) ∧
      N.IsKFlat ∧
      (∀ n : ℤ, SheafOfModules.IsFlat (N.X n)) ∧
      QuasiIso c := sorry

end AlgebraicGeometry.RingedSpace.CochainComplex
