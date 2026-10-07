module

public import ReasLib.CategoryTheory.Fibered.Inertia.Based.Construction

/-!
# Computations for based relative and absolute inertia

This leaf exposes the total categories and projections of the based inertia
owners, and the total functors underlying their canonical forgetful maps.
-/

@[expose] public section

universe u v uX vX uY vY

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}

/-- The total category of based relative inertia is the neutral relative-inertia category. -/
@[simp, stacks 034I "based relative-inertia total category"]
theorem relativeInertia.obj (F : X ⥤ᵇ Y) :
    (relativeInertia F).obj = CategoryTheory.RelativeInertia F.toFunctor := sorry
/- Proof strategy: unfold `relativeInertia` and `BasedCategory.ofFunctor`. -/

/-- The based relative-inertia projection is the neutral relative-inertia projection. -/
@[simp, stacks 034I "based relative-inertia projection"]
theorem relativeInertia.p (F : X ⥤ᵇ Y) :
    (relativeInertia F).p =
      CategoryTheory.RelativeInertia.projection F.toFunctor X.p := sorry
/- Proof strategy: unfold `relativeInertia` and `BasedCategory.ofFunctor`. -/

/- The bundled projection has the same object and arrow formulas as the neutral owner. -/
/-- The based relative-inertia projection sends an object to the base of its underlying object. -/
@[simp, stacks 034I "based relative-inertia projection on objects"]
theorem relativeInertia.p.obj (F : X ⥤ᵇ Y) (A : (relativeInertia F).obj) :
    (relativeInertia F).p.obj A = X.p.obj A.obj := sorry

/-- The based relative-inertia projection sends an arrow to the base of its underlying inertia
arrow. -/
@[simp, stacks 034I "based relative-inertia projection on arrows"]
theorem relativeInertia.p.map (F : X ⥤ᵇ Y)
    {A B : (relativeInertia F).obj} (φ : A ⟶ B) :
    (relativeInertia F).p.map φ = X.p.map (CategoryTheory.RelativeInertia.hom φ) := sorry

/-- The total category of based absolute inertia is the neutral self-relative-inertia category,
so its chosen automorphisms are precisely those vertical over the base. -/
@[simp, stacks 034I "based absolute-inertia total category"]
theorem inertia.obj (X : BasedCategory.{vX, uX} C) :
    (inertia X).obj = CategoryTheory.RelativeInertia X.p := sorry
/- Proof strategy: unfold `inertia`, `relativeInertia`, `BasedCategory.toBase`, and the neutral
relative-inertia specialization. -/

/-- The absolute-inertia projection is the self-relative-inertia projection of `X.p`. -/
@[simp, stacks 034I "based absolute-inertia projection"]
theorem inertia.p (X : BasedCategory.{vX, uX} C) :
    (inertia X).p = CategoryTheory.RelativeInertia.projection X.p X.p := sorry
/- Proof strategy: unfold `inertia`, `relativeInertia`, and `BasedCategory.toBase`. -/

/-- The based absolute-inertia projection sends an object to the base of its underlying object. -/
@[simp, stacks 034I "based absolute-inertia projection on objects"]
theorem inertia.p.obj (X : BasedCategory.{vX, uX} C) (A : (inertia X).obj) :
    (inertia X).p.obj A = X.p.obj A.obj := sorry

/-- The based absolute-inertia projection sends an arrow to the base of its underlying inertia
arrow. -/
@[simp, stacks 034I "based absolute-inertia projection on arrows"]
theorem inertia.p.map (X : BasedCategory.{vX, uX} C)
    {A B : (inertia X).obj} (φ : A ⟶ B) :
    (inertia X).p.map φ = X.p.map (CategoryTheory.RelativeInertia.hom φ) := sorry

/-- The underlying functor of the based relative-inertia structure map is the neutral forgetful
functor. -/
@[simp, stacks 042H "based relative-inertia forgetful functor"]
theorem RelativeInertia.forget.toFunctor (F : X ⥤ᵇ Y) :
    (RelativeInertia.forget F).toFunctor =
      CategoryTheory.RelativeInertia.forget F.toFunctor := sorry
/- Proof strategy: unfold `RelativeInertia.forget`. -/

/-- The underlying functor of the absolute-inertia structure map is the corresponding neutral
relative-inertia forgetful functor. -/
@[simp, stacks 042H "based absolute-inertia forgetful functor"]
theorem Inertia.forget.toFunctor (X : BasedCategory.{vX, uX} C) :
    (Inertia.forget X).toFunctor =
      CategoryTheory.RelativeInertia.forget X.toBase.toFunctor := sorry
/- Proof strategy: unfold `Inertia.forget` and `RelativeInertia.forget`. -/

end BasedCategory
end CategoryTheory
