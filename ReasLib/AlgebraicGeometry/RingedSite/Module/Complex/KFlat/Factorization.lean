module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.KFlat.Resolution
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.QuasiIso
import Mathlib.Tactic.CrossRefAttribute

/-!
# K-flat factorization on ringed-site module complexes

This leaf owns the homotopy-factorization interface separately from the construction of K-flat
resolutions.  The intermediate complex and its comparison maps are exposed directly; no wrapper
structure hides the homotopy, K-flatness, or quasi-isomorphism clauses.
-/

@[expose] public section

open CategoryTheory HomologicalComplex

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]

/-- Lemma 21.17.17 (0G7D): a morphism from a K-flat complex factors up to homotopy through a
quasi-isomorphism with K-flat source. -/
@[stacks 0G7D "K-flat homotopy factorization"]
theorem exists_homotopy_factorization_through_kFlat_quasiIso
    (K L : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)
    (a : K ⟶ L) (hK : K.IsKFlat) :
    ∃ (N : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)
      (b : K ⟶ N) (c : N ⟶ L),
      Nonempty (Homotopy a (b ≫ c)) ∧ N.IsKFlat ∧ QuasiIso c := sorry

/-- Lemma 21.17.17 (0G7D): if the source is termwise flat, the intermediate K-flat complex may be
chosen termwise flat as well. -/
@[stacks 0G7D "termwise-flat K-flat homotopy factorization"]
theorem exists_termwiseFlat_homotopy_factorization_through_kFlat_quasiIso
    (K L : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)
    (a : K ⟶ L) (hK : K.IsKFlat)
    (hFlatK : IsTermwiseFlat K) :
    ∃ (N : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)
      (b : K ⟶ N) (c : N ⟶ L),
      Nonempty (Homotopy a (b ≫ c)) ∧
      N.IsKFlat ∧
      IsTermwiseFlat N ∧
      QuasiIso c := sorry

/-- Lemma 21.17.17 (0G7D): degreewise flatness is an equivalent source-facing form of the
termwise-flat refinement. -/
@[stacks 0G7D "degreewise-flat K-flat homotopy factorization"]
theorem exists_homotopy_factorization_through_kFlat_quasiIso_of_termwiseFlat
    (K L : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)
    (a : K ⟶ L) (hK : K.IsKFlat)
    (hFlatK : ∀ n : ℤ, IsFlat 𝒪 (K.X n)) :
    ∃ (N : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)
      (b : K ⟶ N) (c : N ⟶ L),
      Nonempty (Homotopy a (b ≫ c)) ∧
      N.IsKFlat ∧
      (∀ n : ℤ, IsFlat 𝒪 (N.X n)) ∧
      QuasiIso c := sorry

end SheafOfModules.RingedSite
