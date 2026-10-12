/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point
import StacksCheckRecall

namespace AlgebraicGeometry

universe u

/- Lemma 29.16.5: if `f : T ⟶ S` is locally of finite type, then the image of the finite type
points of `T` is contained in the finite type points of `S`.
-/
@[stacks 02J3] #check
  (AlgebraicGeometry.LocallyOfFiniteType.image_finiteTypePoints_subset :
    ∀ {T S : Scheme.{u}} (f : T ⟶ S) [LocallyOfFiniteType f],
      f '' finiteTypePoints T ⊆ finiteTypePoints S)

end AlgebraicGeometry
