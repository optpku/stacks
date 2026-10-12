/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFormula
import StacksCheckRecall

open AlgebraicGeometry

universe u

/-
Lemma 29.52.4 (1): for a dominant locally finite-type morphism of integral schemes with locally
Noetherian target, the dimension of the source is at most the dimension of the target plus the
transcendence degree of the induced extension of function fields.
-/
@[stacks 02JX] #check
  (AlgebraicGeometry.Scheme.Hom.DimensionFormula.topologicalKrullDim_le_add_functionFieldTrdeg :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Y]
      [IsIntegral X] [IsIntegral Y] [IsDominant f],
      topologicalKrullDim X ≤
        topologicalKrullDim Y +
          (f.functionFieldTrdeg f.map_genericPoint_eq_of_isDominant : WithBot ℕ∞))

/-
Lemma 29.52.4 (2): under the same hypotheses, if the underlying map is closed, the dimension of
the source equals the dimension of the target plus the transcendence degree of the induced
extension of function fields.
-/
@[stacks 02JX] #check
  (AlgebraicGeometry.Scheme.Hom.DimensionFormula.topologicalKrullDim_eq_add_functionFieldTrdeg_of_isClosedMap :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Y]
      [IsIntegral X] [IsIntegral Y] [IsDominant f],
      IsClosedMap f.base →
        topologicalKrullDim X =
          topologicalKrullDim Y +
            (f.functionFieldTrdeg f.map_genericPoint_eq_of_isDominant : WithBot ℕ∞))
