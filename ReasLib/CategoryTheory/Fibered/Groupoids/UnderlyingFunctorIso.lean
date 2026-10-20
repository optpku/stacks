module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom

/-!
# Underlying functor isomorphisms

An isomorphism between morphisms of categories fibred in groupoids induces the corresponding
natural isomorphism between their total-category functors.
-/

@[expose] public section

universe v u

namespace CategoryTheory.FiberedCategoryOver.Groupoids

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Groupoids C}

/-- The natural isomorphism between underlying total-category functors induced by an
isomorphism of morphisms of categories fibred in groupoids. -/
def toFunctorIso {F G : X ⟶ Y} (e : F ≅ G) :
    toFunctor F ≅ toFunctor G :=
  Pseudofunctor.mapToFunctorIso (toBased C).toPseudofunctor e

/-- The forward transformation of an underlying total-functor isomorphism is the underlying
natural transformation of the forward owner `2`-cell. -/
@[simp]
theorem toFunctorIso.hom {F G : X ⟶ Y} (e : F ≅ G) :
    (toFunctorIso e).hom = e.hom.hom.toNatTrans := sorry

/-- The inverse transformation of an underlying total-functor isomorphism is the underlying
natural transformation of the inverse owner `2`-cell. -/
@[simp]
theorem toFunctorIso.inv {F G : X ⟶ Y} (e : F ≅ G) :
    (toFunctorIso e).inv = e.inv.hom.toNatTrans := sorry

/-- The forward component of an underlying total-functor isomorphism is the total-category
component of the forward owner `2`-cell. -/
@[simp]
theorem toFunctorIso.hom.app {F G : X ⟶ Y} (e : F ≅ G) (x : X.total) :
    (toFunctorIso e).hom.app x = e.hom.hom.toNatTrans.app x := sorry

/-- The inverse component of an underlying total-functor isomorphism is the total-category
component of the inverse owner `2`-cell. -/
@[simp]
theorem toFunctorIso.inv.app {F G : X ⟶ Y} (e : F ≅ G) (x : X.total) :
    (toFunctorIso e).inv.app x = e.inv.hom.toNatTrans.app x := sorry

/-- Forgetting the identity owner isomorphism gives the identity total-functor isomorphism. -/
@[simp]
theorem toFunctorIso.refl (F : X ⟶ Y) :
    toFunctorIso (Iso.refl F) = Iso.refl (toFunctor F) := sorry

/-- Forgetting owner isomorphisms commutes with symmetry. -/
@[simp]
theorem toFunctorIso.symm {F G : X ⟶ Y} (e : F ≅ G) :
    toFunctorIso e.symm = (toFunctorIso e).symm := sorry

/-- Forgetting owner isomorphisms preserves their composition. -/
theorem toFunctorIso.trans {F G H : X ⟶ Y} (e : F ≅ G) (d : G ≅ H) :
    toFunctorIso (e ≪≫ d) = toFunctorIso e ≪≫ toFunctorIso d := sorry

end CategoryTheory.FiberedCategoryOver.Groupoids
