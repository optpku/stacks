module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import StacksCheckRecall

@[expose] public section

universe w v vA u₁ u₂

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {A : Type u₁} [Category.{vA} A]
variable {C : Type u₂} [Bicategory.{w, v} C]

/- There are two distinct abstraction levels in the source. Its ordinary functor `A ⥤ C` needs
`C` to be strict: only then do the objects and `1`-morphisms of `C` form an ordinary category.
The weak-functor data itself does not need strictness. As in the nLab definition, it is meaningful
between arbitrary bicategories, so the canonical owner is `LocallyDiscrete A ⥤ᵖ C` with no
`Bicategory.Strict C` assumption.

Stacks chooses the comparison cells
`𝟙 (Φ.obj (LocallyDiscrete.mk x)) ⟶ Φ.map ((𝟙 x).toLoc)` and
`Φ.map ((f ≫ g).toLoc) ⟶ Φ.map f.toLoc ≫ Φ.map g.toLoc`. Mathlib stores the corresponding constraints as
isomorphisms, so the exact source-facing cells are `mapId.inv` and `mapComp.hom`. The nLab
presentation displays the inverse orientation for composition and explicitly notes that either
orientation gives the same pseudofunctor notion because the constraints are invertible. Thus
neither a second weak-functor structure nor a convention-only wrapper is needed.
`LocallyDiscrete.mkPseudofunctor` suppresses the uniquely determined action on
`2`-morphisms and asks for precisely the remaining comparisons and three coherence laws.
`Functor.toPseudofunctor'` is the separate canonical bridge that promotes an ordinary functor when
the target really is strict. -/

section StrictTarget

variable [Bicategory.Strict C]

/- Definition 4.29.5 (1): an ordinary functor from `A` to the strict `2`-category `C` ignores
`2`-morphisms and is a functor `A ⥤ C` into its underlying category. -/
@[stacks 003N "(1)"]
#check (A ⥤ C)

/- Definition 4.29.5 (2): a weak or pseudo functor from `A` to `C` is canonically a
pseudofunctor `LocallyDiscrete A ⥤ᵖ C`. -/
@[stacks 003N "(2)"]
#check (LocallyDiscrete A ⥤ᵖ C)

/- An ordinary functor into the underlying category of a strict bicategory canonically determines
a pseudofunctor with equality-induced comparison isomorphisms. -/
#check Functor.toPseudofunctor'

end StrictTarget

section WeakFunctor

/- The canonical constructor works at the generalized, and mathematically natural, level of an
arbitrary bicategory target. -/
#check LocallyDiscrete.mkPseudofunctor

variable (Φ : LocallyDiscrete A ⥤ᵖ C)

/- The two source-oriented structural cells are the following existing projections:

```
                (Φ.mapId (LocallyDiscrete.mk a)).inv
𝟙 (Φ.obj (LocallyDiscrete.mk a)) ───────────────────────▶ Φ.map ((𝟙 a).toLoc)

                   (Φ.mapComp f.toLoc g.toLoc).hom
Φ.map ((f ≫ g).toLoc) ─────────────────────────────▶ Φ.map f.toLoc ≫ Φ.map g.toLoc
```

The constructor's associativity and two unitality inputs are the invariant bicategorical forms
of the three strict equations displayed by Stacks. -/
#check (fun (a : A) ↦ (Φ.mapId (LocallyDiscrete.mk a)).inv :
  ∀ a : A, 𝟙 (Φ.obj (LocallyDiscrete.mk a)) ⟶ Φ.map ((𝟙 a).toLoc))

#check (fun {a b c : A} (f : a ⟶ b) (g : b ⟶ c) ↦
    (Φ.mapComp f.toLoc g.toLoc).hom :
  ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c),
    Φ.map ((f ≫ g).toLoc) ⟶ Φ.map f.toLoc ≫ Φ.map g.toLoc)

end WeakFunctor

end CategoryTheory
