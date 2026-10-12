/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Pushout.AdmissibleSpan

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Pushout
namespace IsAdmissibleSpan

/- Lemma 37.67.2: every point of the target of an admissible span has an affine
neighborhood whose inverse image agrees with that of an affine open in the other target. -/
@[stacks 0ECJ] #check
  (AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.exists_affineOpen_preimage_eq :
    ∀ {S : Scheme.{u}} {Z X Y : Over S} {i : Z ⟶ X} {j : Z ⟶ Y}
      [IsAdmissibleSpan i j] (y : Y.left),
      ∃ (U : X.left.Opens) (_ : IsAffineOpen U) (V : Y.left.Opens) (_ : IsAffineOpen V),
        i.left ⁻¹ᵁ U = j.left ⁻¹ᵁ V ∧ y ∈ V)

end IsAdmissibleSpan
end Pushout
end Scheme
end AlgebraicGeometry
