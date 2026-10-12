/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Skeleton.Generated.Abelian
import StacksCheckRecall

/-!
@stack 018U

# Lemma 14.21.10 compatibility facade

ReasLib owns the image identification, its monomorphic subobject form, and the canonical
isomorphisms identifying the simplicial skeleton with bounded-degree generation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialObject

universe u v

namespace CategoryTheory.SimplicialObject.Skeleton

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (n : ℕ) (U : SimplicialObject A)

/- Lemma 14.21.10 (1): the image of the skeleton counit is the generated subobject. -/
@[stacks 018U "Lemma 14.21.10 (1)"]
#check (counit.imageSubobject_eq_generated n U :
  imageSubobject ((skAdj n).counit.app U) = U.generated n)

/- Lemma 14.21.10 (2): the resulting canonical subobject identification. -/
@[stacks 018U "Lemma 14.21.10 (2)"]
#check (generated.subobjectIso n U :
  (sk n).obj U ≅ (U.generated n : SimplicialObject A))

#check (counit.subobject_eq_generated n U :
  Subobject.mk ((skAdj n).counit.app U) = U.generated n)

#check (generated.isoApp n U :
  (sk n).obj U ≅ SimplicialObject.generated.obj U n)

#check (generated.iso (A := A) n :
  sk n ≅ SimplicialObject.generated.functor n)

#check (inferInstance : Mono ((skAdj n).counit.app U))

end CategoryTheory.SimplicialObject.Skeleton
