module

public import ReasLib.AlgebraicTopology.SimplicialObject.Skeleton.NormalizedMoore
import StacksCheckRecall

/-!
@stack 017Y

# Lemma 14.18.9 compatibility facade

The bounded-degree generated subobject and all of its structural API are owned by ReasLib.  This
file records the three source clauses without rebuilding finite indexing or local mono instances.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialObject Opposite
open AlgebraicTopology
open scoped Simplicial

universe u v

namespace CategoryTheory.SimplicialObject

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (U : SimplicialObject A) (n m i : ℕ)

/- Lemma 14.18.9 (1): in each degree, bounded-degree generation is the least upper bound of
the images of all structure maps from degrees at most `n`. -/
@[stacks 017Y "Lemma 14.18.9 (1)"]
#check (generated.degree_isLUB U n m :
  IsLUB
    (setOf fun P : Subobject (U.obj (op ⦋m⦌)) ↦
      ∃ i, i ≤ n ∧ ∃ θ : ⦋m⦌ ⟶ ⦋i⦌,
        P = imageSubobject (U.map θ.op))
    (generated.degree U n ⦋m⦌))

/- These degreewise least upper bounds assemble into the canonical generated simplicial
subobject. -/
#check (U.generated n : Subobject U)

/- Lemma 14.18.9 (2): the generated subobject agrees with `U` in degrees at most `n`. -/
@[stacks 017Y "Lemma 14.18.9 (2)"]
#check (generated.degree_eq_top_of_le U : i ≤ n → generated.degree U n ⦋i⦌ = ⊤)

/- Lemma 14.18.9 (3): its lower-face normalized Moore object vanishes above degree `n`. -/
@[stacks 017Y "Lemma 14.18.9 (3)"]
#check (generated.normalizedMoore.lowerFace.eq_bot_of_lt U :
  n < m → normalizedMoore.lowerFace.subobject
    (U.generated n : SimplicialObject A) m = ⊥)

end CategoryTheory.SimplicialObject
