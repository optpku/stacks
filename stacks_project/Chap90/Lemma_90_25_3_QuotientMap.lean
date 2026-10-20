module

public import ReasLib.CategoryTheory.Groupoid.KernelPair.Quotient

/-!
# Canonical morphism from a kernel-pair quotient

A morphism `f : U ⟶ F` of categories cofibered in groupoids induces a based functor
`[f] : [U/R] ⥤ᵇ F` over `C`, sending a Grothendieck object `(T, x)` to the image of `x`
under `f` and a Grothendieck arrow to the composite of the image lift with the inverse of
the corresponding kernel-pair isomorphism.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

noncomputable section

universe u v w

namespace CategoryTheory.GroupoidInFunctors

variable {C : Type u} [Category.{v} C]
variable {U : C ⥤ Type (max v w)}
variable {F : CofiberedCategoryOver.Groupoids.{u, v, max u (max v w), v} C}

#check (CategoryTheory.GroupoidInFunctors.quotientMapHom :
  ∀ (f : Functor.ofTypeValued U ⟶ F) {p q : (ofMorphism f).quotient.total},
    (p ⟶ q) → (imageObj f p.base p.fiber ⟶ imageObj f q.base q.fiber))

#check (CategoryTheory.GroupoidInFunctors.quotientMapFunctor :
  ∀ (f : Functor.ofTypeValued U ⟶ F), (ofMorphism f).quotient.total ⥤ F.total)

#check (CategoryTheory.GroupoidInFunctors.quotientMap :
  ∀ (f : Functor.ofTypeValued U ⟶ F),
    (ofMorphism f).quotient.toBasedCategory ⥤ᵇ F.toBasedCategory)

#check (CategoryTheory.GroupoidInFunctors.quotientMap_obj :
  ∀ (f : Functor.ofTypeValued U ⟶ F) (T : C) (x : U.obj T),
    (quotientMap f).obj ⟨T, x⟩ = imageObj f T x)

#check (CategoryTheory.GroupoidInFunctors.quotientMap_full :
  ∀ (f : Functor.ofTypeValued U ⟶ F), (quotientMap f).Full)

#check (CategoryTheory.GroupoidInFunctors.quotientMap_faithful :
  ∀ (f : Functor.ofTypeValued U ⟶ F), (quotientMap f).Faithful)

#check (CategoryTheory.GroupoidInFunctors.quotientMap_isEquivalence :
  ∀ (f : Functor.ofTypeValued U ⟶ F)
    [(CofiberedCategoryOver.Groupoids.toBasedFunctor f).EssSurj],
    BasedFunctor.IsEquivalence (quotientMap f))

end CategoryTheory.GroupoidInFunctors
