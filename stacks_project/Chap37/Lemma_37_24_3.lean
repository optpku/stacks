/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.NowhereDenseFiber

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom
namespace FiniteType

/- Lemma 37.24.3: for a finite-type morphism to an irreducible scheme, a closed subset
whose trace on the generic fiber is nowhere dense has nowhere-dense traces on every fiber over
some nonempty open subset of the base. -/
@[stacks 054X]
#check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.exists_open_isNowhereDense_fiber :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] [IrreducibleSpace Y]
      (Z : Set X), IsClosed Z →
        IsNowhereDense ((f.fiberι (genericPoint Y)) ⁻¹' Z) →
          ∃ V : Y.Opens, Nonempty V ∧
            ∀ y : Y, y ∈ V → IsNowhereDense ((f.fiberι y) ⁻¹' Z))

end FiniteType
end Hom
end Scheme
end AlgebraicGeometry
