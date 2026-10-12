/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat.ModuleCat.Monoidal
public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat.QuasiIso
public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat.TermwiseFlat.QuasiIso
public import ReasLib.Algebra.Homology.HomologicalComplex.MonoEpi
import Mathlib.Tactic.CrossRefAttribute

/-!
# K-flat resolutions of module complexes

@stack 06Y4

Every unbounded complex of modules admits a termwise-surjective quasi-isomorphism from a
K-flat complex with flat terms.  The resolution statements are accompanied by the canonical
localization-cover conditions consumed by the K-flat derived-category API.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- Every cochain complex of `R`-modules admits a termwise-epimorphic quasi-isomorphism from a
K-flat cochain complex with flat terms. -/
@[stacks 06Y4 "K-flat resolution"]
theorem exists_termwiseEpi_kFlatResolution
    (M : CochainComplex (ModuleCat R) ℤ) :
    ∃ (K : CochainComplex (ModuleCat R) ℤ) (f : K ⟶ M),
      K.IsKFlat ∧ K.IsTermwiseFlat ∧ QuasiIso f ∧ ∀ i : ℤ, Epi (f.f i) := sorry

/-- Complex-level form of a K-flat resolution: the comparison itself is an epimorphism. -/
theorem exists_epi_kFlatResolution
    (M : CochainComplex (ModuleCat R) ℤ) :
    ∃ (K : CochainComplex (ModuleCat R) ℤ) (f : K ⟶ M),
      K.IsKFlat ∧ K.IsTermwiseFlat ∧ QuasiIso f ∧ Epi f := sorry

end CochainComplex

namespace ModuleCat.KFlat

/-- Module complexes have enough K-flat objects for the canonical full-subcategory
localization model.  This remains an explicit theorem while its proof is deferred, so it cannot
silently choose downstream localization data through typeclass search. -/
@[stacks 06Y4 "K-flat localization cover"]
theorem hasResolutions (R : Type u) [CommRing R] :
    HomotopyCategory.KFlat.HasResolutions (ModuleCat R) := sorry

namespace TermwiseFlat

/-- Module complexes have enough K-flat termwise-flat models for the good-model localization. -/
@[stacks 06Y4 "K-flat termwise-flat localization cover"]
theorem hasResolutions (R : Type u) [CommRing R] :
    HomotopyCategory.KFlat.TermwiseFlat.HasResolutions (ModuleCat R) := sorry

end TermwiseFlat

end ModuleCat.KFlat
