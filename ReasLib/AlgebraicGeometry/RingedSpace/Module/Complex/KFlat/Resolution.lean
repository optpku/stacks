/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Flat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.KFlat.Resolution
import Mathlib.Tactic.CrossRefAttribute

/-!
# K-flat resolutions on ringed spaces

This leaf specializes the ringed-site resolution theorem to complexes of `𝒪_X`-modules.  The
public surface uses the canonical `IsKFlat` and `IsTermwiseFlat` predicates and relies on the
shared opens-site instances instead of rebuilding them in a chapter file.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory HomologicalComplex
open SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.CochainComplex

variable {X : RingedSpace.{u}}

/-- Lemma 20.26.12 (06YF): every complex of `𝒪_X`-modules has a termwise-epimorphic
quasi-isomorphic replacement which is K-flat and termwise flat. -/
@[stacks 06YF "ringed-space termwise-epimorphic K-flat resolution"]
theorem exists_termwiseEpi_kFlatResolution
    (𝒢 : CochainComplex (Modules X) ℤ) :
    ∃ (K : CochainComplex (Modules X) ℤ) (α : K ⟶ 𝒢),
      K.IsKFlat ∧
      HomologicalComplex.IsTermwiseFlat K ∧
      QuasiIso α ∧
      ∀ n : ℤ, Epi (α.f n) := sorry

/-- The complex-level companion of the ringed-space K-flat resolution has an epimorphic
comparison map. -/
@[stacks 06YF "ringed-space K-flat resolution with an epimorphic comparison"]
theorem exists_epi_kFlatResolution
    (𝒢 : CochainComplex (Modules X) ℤ) :
    ∃ (K : CochainComplex (Modules X) ℤ) (α : K ⟶ 𝒢),
      K.IsKFlat ∧
      HomologicalComplex.IsTermwiseFlat K ∧
      QuasiIso α ∧
      Epi α := sorry

end AlgebraicGeometry.RingedSpace.CochainComplex
