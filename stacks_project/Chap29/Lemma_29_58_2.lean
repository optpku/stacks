/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField.Factorization
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

/- Lemma 29.58.2: if `f : Y ⟶ X` maps a reduced scheme into a subset `E` of a locally
Noetherian scheme and the points of `E` have no nontrivial specializations among themselves,
then `f` factors through the canonical map from the coproduct of their residue-field spectra. -/
@[stacks 0H1N] #check
  (AlgebraicGeometry.Scheme.Hom.ResidueField.exists_factorization_pointSpectrumCoproduct_of_range_subset :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X) (E : Set X)
      [AlgebraicGeometry.IsLocallyNoetherian X] [AlgebraicGeometry.IsReduced Y],
      (∀ ⦃x x' : X⦄, x ∈ E → x' ∈ E → Specializes x x' → x = x') →
      Set.range f ⊆ E →
      ∃ g : Y ⟶ AlgebraicGeometry.pointSpectrumCoproduct X E,
        g ≫ AlgebraicGeometry.pointSpectrumCoproductTo X E = f)
