module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
import StacksCheckRecall

@[expose] public section

universe vS uS v u

namespace CategoryTheory

variable (C : Type uS) [Category.{vS} C]
variable (X Y : BasedCategory.{v, u} C)
variable (F G : X ⥤ᵇ Y)

/-!
`BasedCategory.bicategory` is the canonical mathlib owner for `Cat/C`: its objects are
`BasedCategory C`, its `1`-morphisms are `BasedFunctor`s whose projection triangles commute
strictly, and its `2`-morphisms are vertical `BasedNatTrans`s. The project-level reusable API for
strict isomorphisms, fibre functors, and equivalences over the base lives in
`CategoryTheory.Fibered.BasedCategory`; this numbered module only records the textbook entry.
-/

/- Definition 4.32.1: an object of `Cat/C` is a category equipped with a projection functor to
`C`, represented by `CategoryTheory.BasedCategory C`. -/
@[stacks 003Y "objects as categories equipped with a projection to the base"]
#check (CategoryTheory.BasedCategory.{v, u} C :
  Type max (u + 1) (v + 1) uS vS)

/- Definition 4.32.1: a `1`-morphism in `Cat/C` is a functor strictly commuting with the
projections, represented by `X ⥤ᵇ Y`. -/
@[stacks 003Y "1-morphisms as functors strictly commuting with projections"]
#check (CategoryTheory.BasedFunctor X Y : Type max u v)

/- Definition 4.32.1: a `2`-morphism in `Cat/C` is a natural transformation whose components lie
over identity morphisms, represented by `CategoryTheory.BasedNatTrans`. -/
@[stacks 003Y "2-morphisms as natural transformations vertical over identities"]
#check (CategoryTheory.BasedNatTrans F G : Type max u v)

/- Definition 4.32.1: the category of `1`-morphisms between two objects of `Cat/C` has based
functors as objects and based natural transformations as morphisms. -/
@[stacks 003Y "hom-category of 1-morphisms and vertical 2-morphisms"]
#check (CategoryTheory.BasedNatTrans.homCategory X Y :
  Category.{max u v} (X ⥤ᵇ Y))

/- Definition 4.32.1: the preceding objects, `1`-morphisms, and `2`-morphisms carry the canonical
strict bicategory structure on `CategoryTheory.BasedCategory C`. -/
@[stacks 003Y "strict bicategory structure on categories over the base"]
#check (CategoryTheory.BasedCategory.bicategory (𝒮 := C) :
  Bicategory.{max u v, max u v} (BasedCategory.{v, u} C))

/- The bicategory above is strict, as witnessed by the canonical `Strict` instance. -/
@[stacks 003Y "strictness of the bicategory of categories over the base"]
#check (inferInstance : Bicategory.Strict (BasedCategory.{v, u} C))

end CategoryTheory
