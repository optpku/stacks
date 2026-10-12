/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.NegStage
public import ReasLib.CategoryTheory.Filtration.Complex.StageSequence.Naturality

/-!
# Naturality of negative filtration stages

This leaf exposes the componentwise and diagrammatic functoriality of the
negative-stage facade.  The actual construction lives in `NegStage`; the
statements here are the convenient names used by truncation and spectral
sequence clients.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.NegStage

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]

/-- The negative-stage inclusions, natural in the filtered complex. -/
@[stacks 0D8Z "natural transformation from negative filtration stages to the underlying complex"]
noncomputable abbrev toConstNatTrans :
    functor (A := A) ⟶ underlyingFunctor ⋙ (Functor.const ℕ) :=
  StageSequence.toUnderlyingNatTrans index index_anti

/-- A component of `toConstNatTrans` is the canonical negative-stage transformation to the
constant underlying complex. -/
@[simp, stacks 0D8Z "component of the negative-stage inclusion natural transformation"]
theorem toConstNatTrans_app (K : FilteredComplex A) :
    (toConstNatTrans (A := A)).app K = toConst K := sorry

/-- The successor comparison is natural with respect to a map of filtered complexes. -/
@[reassoc, stacks 0D8Z]
theorem step_naturality {K L : FilteredComplex A} (f : K ⟶ L) (n : ℕ) :
    step K n ≫ mapApp f (n + 1) = mapApp f n ≫ step L n := sorry

end CategoryTheory.FilteredComplex.NegStage
