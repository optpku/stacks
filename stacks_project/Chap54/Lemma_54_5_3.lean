/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.NormalizedDomination
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 54.5.3 -/
@[stacks 0BBT]
#check
  (AlgebraicGeometry.Scheme.Hom.exists_normalizedBlowupSequence_lift :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X),
      [IsNoetherian X] → [Scheme.Nagata X] → [IsProper f] → [IsBirational f] →
        topologicalKrullDim X = 2 →
          ∃ (Z : Scheme.{u}) (s : Scheme.NormalizedBlowupSequence X.normalization Z)
            (g : Z ⟶ Y), g ≫ f = s.toSource ≫ X.normalizationTo)

end AlgebraicGeometry.Scheme.Hom
