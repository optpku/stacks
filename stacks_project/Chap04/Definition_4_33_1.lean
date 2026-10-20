module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

variable {S : Type u₁} [Category.{v₁} S]
variable {C : Type u₂} [Category.{v₂} C]
variable (p : S ⥤ C) {V U : C} {x y : S}
variable (f : V ⟶ U) (φ : x ⟶ y)


/- The source needs the predicate characterized by bijectivity of the postcomposition-and-image
map. `Functor.IsStronglyCartesian` and `IsStronglyCartesian.universal_property` are the installed
Cartesian owner and access API; `Functor.IsStronglyCocartesian` is the dual notion and reverses the
factorization direction. The owner's explicit base arrow `f` is only the `IsHomLift` packaging:
specializing it to `p.map φ` recovers the source's arrow-only wording. Recalling the owner exposes
its reusable lift, factorization, and composition API without a parallel chapter predicate. -/

/- Definition 4.33.1: a strongly `𝒞`-cartesian morphism for a category over `𝒞` is the canonical
predicate `CategoryTheory.Functor.IsStronglyCartesian`. -/
@[stacks 02XK "strongly cartesian morphisms over a base category"]
#check (CategoryTheory.Functor.IsStronglyCartesian p f φ : Prop)
