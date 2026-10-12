/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.PithStrict
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

open Bicategory
open scoped Bicategory

/-
Mathlib 4.32's `Pith B` is the canonical homwise core of a bicategory: it keeps every object and
`1`-morphism of `B` and replaces each hom-category by `Core`. Consequently Example 4.30.2 is a
direct use of `Pith Cat`, not a new category-of-natural-isomorphisms wrapper. The projection
`CoreHom.iso` followed by `Cat.Hom.toNatIso` below makes the source phrase “isomorphisms of
functors” explicit without creating a redundant conversion API.

Mathlib already supplies the bicategory and locally-groupoidal structures on every `Pith B`, but
does not supply strictness inheritance. That missing fact is correctly stated once for arbitrary
`[Strict B]`; a `Cat`-specific instance would lose useful generality. The instance head decreases
from `Strict (Pith B)` to `Strict B`, so repeated piths do not create a typeclass loop. No notation
is introduced: `Pith` is already the short canonical owner name, while an item-local symbol would
hide rather than clarify the homwise-core construction.

Import decision: `CategoryTheory.Bicategory.PithStrict` is public because the labeled surface uses
`Pith` and checks the generic strictness instance. `StacksCheckRecall` is plain because it only
elaborates the source annotation.
-/


/- Example 4.30.2: the strict `2`-category `Cat` becomes the canonical `(2,1)`-category
`Pith Cat`, with the same categories and functors and only invertible natural transformations as
`2`-morphisms. -/
@[stacks 003K "categories, functors, and natural isomorphisms"]
#check (Pith Cat.{v, u} : Type max (v + 1) (u + 1))

/- `Pith.inclusion` forgets only the invertibility restriction on `2`-morphisms and exhibits the
homwise core inside the original bicategory. -/
#check Bicategory.Pith.inclusion Cat.{v, u}

/- A `2`-morphism in `Pith Cat` canonically exposes the natural isomorphism required by the
source, rather than merely an arbitrary natural transformation. -/
#check fun {C D : Pith Cat.{v, u}} {F G : C ⟶ D} (η : F ⟶ G) ↦
  Cat.Hom.toNatIso η.iso

/- The generic infrastructure above preserves the strict `2`-category structure of `Cat`. -/
#check (inferInstance : Strict (Pith Cat.{v, u}))

/- Every hom-category of a pith is a groupoid by mathlib's canonical `Pith.homGroupoid`
instance. -/
#check (inferInstance : IsLocallyGroupoid (Pith Cat.{v, u}))

end CategoryTheory
