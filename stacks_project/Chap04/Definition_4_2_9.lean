module

public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Functor.FullyFaithful
import StacksCheckRecall

@[expose] public section


universe v₁ v₂ u₁ u₂

namespace CategoryTheory
namespace Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (F : C ⥤ D)

/- Definition 4.2.9 (1): a functor `F : C ⥤ D` is faithful when every induced map
`F.map : X ⟶ Y → (F.obj X ⟶ F.obj Y)` is injective. -/
@[stacks 001C "faithful functors"]
#check (Faithful F : Prop)

/-
The source asks only for bijectivity of every induced hom-map. Mathlib's `Functor.Full` and
`Functor.Faithful` split this proposition into surjectivity and injectivity, while
`Functor.FullyFaithful` stores inverse maps. The theorem
`Functor.FullyFaithful.nonempty_iff_map_bijective` is the exact source-facing bridge: no
generalization is introduced, and its right-hand side recovers the stated condition verbatim.
Recalling it avoids a redundant local predicate while allowing downstream code to recover the
canonical data owner when needed.
-/

/- Definition 4.2.9 (2): a functor `F : C ⥤ D` is fully faithful when every induced map
`F.map : X ⟶ Y → (F.obj X ⟶ F.obj Y)` is bijective; equivalently,
`Nonempty F.FullyFaithful`. -/
@[stacks 001C "fully faithful functors"]
#check (FullyFaithful.nonempty_iff_map_bijective F :
  Nonempty F.FullyFaithful ↔
    ∀ (X Y : C),
      Function.Bijective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)))

/- Definition 4.2.9 (3): a functor `F : C ⥤ D` is essentially surjective when every `Y : D`
lies in `F.essImage`, meaning that `F.obj X ≅ Y` for some `X : C`. -/
@[stacks 001C "essentially surjective functors"]
#check (EssSurj F : Prop)

end Functor
end CategoryTheory
