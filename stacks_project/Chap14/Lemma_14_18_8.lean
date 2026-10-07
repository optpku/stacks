module

public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.LowerFace
import StacksCheckRecall

/-!
@stack 017X

# Lemma 14.18.8 compatibility facade

The lower-face normalized Moore owner and its restricted last-face morphism live together in
ReasLib, with the inclusion equation exposed as reusable API.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

universe u v

namespace CategoryTheory.SimplicialObject

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (U : SimplicialObject A) (m : ℕ)

/- Lemma 14.18.8: the last face carries the lower-face normalized Moore subobject in degree
`m + 1` into the corresponding subobject in degree `m`. -/
@[stacks 017X]
#check (normalizedMoore.lowerFace.lastFace.le_pullback U m :
  normalizedMoore.lowerFace.subobject U (m + 1) ≤
    (Subobject.pullback (U.δ (Fin.last (m + 1)))).obj
      (normalizedMoore.lowerFace.subobject U m))

/- The resulting restricted last-face morphism is the reusable data attached to the
inclusion. -/
#check (normalizedMoore.lowerFace.lastFace U m :
  (normalizedMoore.lowerFace.subobject U (m + 1) : A) ⟶
    (normalizedMoore.lowerFace.subobject U m : A))

/- The restricted last face agrees with the ambient last face after inclusion. -/
#check normalizedMoore.lowerFace.lastFace.arrow

/- The restricted last face is the differential owned by the lower-face normalized Moore
functor. -/
#check Abelian.DoldKan.N.lowerFace.obj_d

end CategoryTheory.SimplicialObject
