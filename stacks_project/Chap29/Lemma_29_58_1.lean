module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField.Factorization
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 29.58.1: A morphism from a reduced scheme whose set-theoretic image is contained in
one point factors through the canonical morphism from the spectrum of that point's residue field. -/
@[stacks 0H1M] #check
  (AlgebraicGeometry.Scheme.Hom.ResidueField.exists_factorization_of_range_subset_singleton :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) (x : X) [IsReduced Y],
      Set.range f ⊆ {x} →
        ∃ g : Y ⟶ Spec (X.residueField x), g ≫ X.fromSpecResidueField x = f)
