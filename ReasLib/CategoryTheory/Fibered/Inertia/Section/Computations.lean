module

public import ReasLib.CategoryTheory.Fibered.Inertia.Section.Construction

/-!
# Computations for identity sections of based inertia

This leaf exposes the underlying neutral functors and their round-trip laws;
object, automorphism, and arrow readouts live in
`Fibered/Inertia/Computations/Sections`.
-/

@[expose] public section

universe u v u₁ v₁ u₁' v₁'

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans

variable {C : Type u} [Category.{v} C]

section IdentitySection

variable {X : BasedCategory.{v₁, u₁} C} {Y : BasedCategory.{v₁', u₁'} C}

/-- The underlying functor of the based neutral section is the neutral relative-inertia section. -/
@[simp, stacks 04Z3 "based relative-inertia identity-section functor"]
theorem RelativeInertia.identitySection.toFunctor (F : X ⥤ᵇ Y) :
    (RelativeInertia.identitySection F).toFunctor =
      CategoryTheory.RelativeInertia.identitySection F.toFunctor := sorry
/- Proof strategy: unfold `RelativeInertia.identitySection`. -/

/-- The relative neutral section is a right inverse to the relative-inertia forgetful map. -/
@[simp, stacks 04Z3 "based relative-inertia identity-section round trip"]
theorem RelativeInertia.identitySection.comp_forget (F : X ⥤ᵇ Y) :
    RelativeInertia.identitySection F ⋙ RelativeInertia.forget F = 𝟭 X := sorry
/- Proof strategy: apply `BasedFunctor.ext` and use the neutral
`CategoryTheory.RelativeInertia.identitySection.comp_forget` theorem. -/

/-- The underlying functor of the based neutral absolute section is the neutral
self-relative-inertia section. -/
@[simp, stacks 04Z3 "based absolute-inertia identity-section functor"]
theorem Inertia.identitySection.toFunctor (X : BasedCategory.{v₁, u₁} C) :
    (Inertia.identitySection X).toFunctor =
      CategoryTheory.RelativeInertia.identitySection X.toBase.toFunctor := sorry
/- Proof strategy: unfold `Inertia.identitySection`. -/

/-- The absolute neutral section is a right inverse to the absolute-inertia forgetful map. -/
@[simp, stacks 04Z3 "based absolute-inertia identity-section round trip"]
theorem Inertia.identitySection.comp_forget (X : BasedCategory.{v₁, u₁} C) :
    Inertia.identitySection X ⋙ Inertia.forget X = 𝟭 X := sorry
/- Proof strategy: specialize `RelativeInertia.identitySection.comp_forget` to `X.toBase`. -/

end IdentitySection

end BasedCategory
end CategoryTheory
