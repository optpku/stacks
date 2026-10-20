module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj
import StacksCheckRecall

@[expose] public section

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B]
variable (x y : B)
variable (e : x ≌ y)

/- Definition 4.29.4: two objects of a `2`-category are equivalent when there are `1`-morphisms
in both directions whose two composites are `2`-isomorphic to the corresponding identities; the
canonical owner is `Bicategory.Equivalence x y`, written `x ≌ y`.

The owner also stores a triangle identity, but `Equivalence.mkOfAdjointifyCounit` constructs that
coherence from exactly the two source isomorphisms. Thus the canonical owner adds no
existence-level hypothesis. The reusable support is stated for bicategories; adding
`[Bicategory.Strict B]` specializes it back to strict `2`-categories. -/
@[stacks 003L "quasi-inverse 1-morphisms with both composites 2-isomorphic to identities"]
#check (e : Bicategory.Equivalence x y)

/- The canonical constructor recovers the source presentation. With mathlib's diagrammatic
composition, `G ∘ F` is written `F ≫ G` and `F ∘ G` is written `G ≫ F`. -/
#check (Equivalence.mkOfAdjointifyCounit :
  ∀ {F : x ⟶ y} {G : y ⟶ x}, (𝟙 x ≅ F ≫ G) → (G ≫ F ≅ 𝟙 y) → (x ≌ y))

end CategoryTheory
