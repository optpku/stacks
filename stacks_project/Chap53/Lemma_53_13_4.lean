/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Curve.Frobenius
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom
open Scheme.Hom.IsNonconstant

universe u

namespace AlgebraicGeometry.Curve

/- Lemma 53.13.4: for a nonconstant morphism of proper nonsingular curves over a
field of characteristic `p > 0`, with smooth source and purely inseparable induced
function-field extension, there is a unique `n : ℕ` and a unique over-`k` isomorphism
`Y ≅ Scheme.pPowerTwist X.hom n` through which the morphism is
`Scheme.iteratedRelativeFrobenius X.hom n`. -/
@[stacks 0CCZ] #check
  (AlgebraicGeometry.Curve.uniqueIteratedRelativeFrobeniusFactorization :
    ∀ {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
      (X Y : SchemeOverField k) [Curve X] [Curve Y]
      [Scheme.Regular X.left] [Scheme.Regular Y.left]
      [IsProper X.hom] [IsProper Y.hom] [Smooth X.hom]
      (f : X ⟶ Y) (hf : f.left.IsNonconstant)
      (h_pi : (f.left.functionFieldMap
        (@map_genericPoint_eq_of_isDominant _ _ f.left
          inferInstance inferInstance (isDominant_of_curves hf))).IsPurelyInseparable),
      ∃! n : ℕ, ∃! e : Y ≅
        @Scheme.pPowerTwist p inferInstance _ _ X.hom inferInstance n,
        f ≫ e.hom =
          @Scheme.iteratedRelativeFrobenius p inferInstance _ _ X.hom inferInstance n)

end AlgebraicGeometry.Curve
