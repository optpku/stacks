/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.ResidueFieldTrdeg
import StacksCheckRecall

@[expose] public section

open scoped ENat

/- Lemma 35.33.7: for `r : ℕ∞`, having residue-field transcendence degree `r` is
étale local on the source-and-target for morphisms of scheme germs. -/
@[stacks 04NK] #check
  (AlgebraicGeometry.Scheme.Germ.MorphismProperty.residueFieldTrdegEq_isEtaleLocal :
    ∀ r : ℕ∞, AlgebraicGeometry.Scheme.Germ.MorphismProperty.IsEtaleLocal
      (AlgebraicGeometry.Scheme.Germ.MorphismProperty.residueFieldTrdegEq r))
