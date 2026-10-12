/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.PurelyInseparableTrace
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry
open AlgebraicGeometry.Scheme.PurelyInseparableTrace

noncomputable section

/- Lemma 54.2.4 -/
@[stacks 0AX6] #check
  (AlgebraicGeometry.Scheme.PurelyInseparableTrace.traceMap :
    ∀ (p : ℕ) [Fact p.Prime]
      (S : SchemeOverField (ZMod p))
      (X Y : Over S.left)
      [IsNoetherian X.left] [IsNoetherian Y.left]
      [IsIntegral X.left] [IsIntegral Y.left]
      (f : Y ⟶ X) [IsFinite f.left] [IsDominant f.left]
      (hX : X.left.isNormal) (hY : Y.left.isNormal)
      (h_pi : (f.left.functionFieldMap
        f.left.map_genericPoint_eq_of_isDominant).IsPurelyInseparable)
      (h_degree : f.left.inducedFunctionFieldDegree = p)
      (i : ℕ) (h_i : 1 ≤ i)
      [SheafOfModules.IsCoherent (Ω[X.hom.toShHom])],
      sourceModule p S X Y f i ⟶ targetModule p S X i)

end
