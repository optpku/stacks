module

public import stacks_project.Chap90.Definition_90_6_1_Prorepresentable
public import stacks_project.Chap90.Remark_90_7_12_Underline
public import stacks_project.Chap90.«90_7_12_1_Yoneda»

/-!
# Formal objects as morphisms from prorepresentable functors

A formal object of a category cofibered in groupoids over `C_Λ` is equivalent
data to a prorepresentable functor `U` together with a based morphism from the
category of elements of `U`.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

namespace FormalObject

open CompleteLocalAlgCat
open Functor.Fiber

noncomputable section

/-- Based functor over `C_Λ` induced by a natural transformation of covariant
Type-valued functors, via the category of elements. -/
def elementsBasedMap {U V : ArtinianLocalAlgCat Λ k ⥤ Type u} (α : U ⟶ V) :
    BasedCategory.ofFunctor (CategoryOfElements.π U) ⥤ᵇ
      BasedCategory.ofFunctor (CategoryOfElements.π V) where
  toFunctor := CategoryOfElements.map α
  w := CategoryOfElements.map_π α

/-- The underlying functor of `elementsBasedMap` is the category-of-elements map. -/
theorem elementsBasedMap_toFunctor {U V : ArtinianLocalAlgCat Λ k ⥤ Type u} (α : U ⟶ V) :
    (elementsBasedMap α).toFunctor = CategoryOfElements.map α := sorry

/-- Remark 90.7.14: giving a formal object of `p` is equivalent to giving a
prorepresentable functor `U : ArtinianLocalAlgCat Λ k ⥤ Type u`, presented by
`e : U ≅ restrictedCoyoneda R`, together with a morphism `U ⟶ F` over `C_Λ`.
The morphism is a based functor `CategoryOfElements.π U ⥤ᵇ p`, and the
comparison sends it to a formal object in `Functor.Fiber (Functor.completion p) R`
by precomposing along `CategoryOfElements.map e.inv` and applying
`fromRestrictedHom`. -/
@[stacks 06HD]
def fromProrepresentableHom (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] {U : ArtinianLocalAlgCat Λ k ⥤ Type u}
    {R : CompleteLocalAlgCat Λ k} (e : U ≅ restrictedCoyoneda R) :
    (BasedCategory.ofFunctor (CategoryOfElements.π U) ⥤ᵇ BasedCategory.ofFunctor p) ⥤
      Functor.Fiber (Functor.completion p) R where
  obj φ := (fromRestrictedHom p R).obj (BasedFunctor.comp (elementsBasedMap e.inv) φ)
  map η := (fromRestrictedHom p R).map (BasedCategory.whiskerLeft (elementsBasedMap e.inv) η)
  map_id := sorry
  map_comp := sorry

/-- Applying `fromProrepresentableHom` is `fromRestrictedHom` after precomposition
along `elementsBasedMap e.inv`. -/
theorem fromProrepresentableHom_obj (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] {U : ArtinianLocalAlgCat Λ k ⥤ Type u}
    {R : CompleteLocalAlgCat Λ k} (e : U ≅ restrictedCoyoneda R)
    (φ : BasedCategory.ofFunctor (CategoryOfElements.π U) ⥤ᵇ BasedCategory.ofFunctor p) :
    (fromProrepresentableHom p e).obj φ =
      (fromRestrictedHom p R).obj (BasedFunctor.comp (elementsBasedMap e.inv) φ) :=
  sorry

/-- The image of a based morphism under `fromProrepresentableHom` is a formal
object with complete local base `R`. -/
theorem fromProrepresentableHom_base (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] {U : ArtinianLocalAlgCat Λ k ⥤ Type u}
    {R : CompleteLocalAlgCat Λ k} (e : U ≅ restrictedCoyoneda R)
    (φ : BasedCategory.ofFunctor (CategoryOfElements.π U) ⥤ᵇ BasedCategory.ofFunctor p) :
    (fiberInclusion.obj ((fromProrepresentableHom p e).obj φ)).base = R :=
  sorry

/-- Precomposition along a prorepresentation is an equivalence, as a transport of
`fromRestrictedHom_isEquivalence`. -/
instance fromProrepresentableHom_isEquivalence (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] {U : ArtinianLocalAlgCat Λ k ⥤ Type u}
    {R : CompleteLocalAlgCat Λ k} (e : U ≅ restrictedCoyoneda R) :
    (fromProrepresentableHom p e).IsEquivalence := sorry

/-- Converse comparison sending a formal object over `R` to a based morphism from a
prorepresentable functor `U` presented by `e`. -/
def toProrepresentableHom (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] {U : ArtinianLocalAlgCat Λ k ⥤ Type u}
    {R : CompleteLocalAlgCat Λ k} (e : U ≅ restrictedCoyoneda R) :
    Functor.Fiber (Functor.completion p) R ⥤
      (BasedCategory.ofFunctor (CategoryOfElements.π U) ⥤ᵇ BasedCategory.ofFunctor p) where
  obj ξ := BasedFunctor.comp (elementsBasedMap e.hom) ((toRestrictedHom R).obj ξ)
  map τ := BasedCategory.whiskerLeft (elementsBasedMap e.hom) ((toRestrictedHom R).map τ)
  map_id := sorry
  map_comp := sorry

/-- On the canonical presentation `U = restrictedCoyoneda R`, the comparison
`fromProrepresentableHom` reduces to `fromRestrictedHom`. -/
theorem fromProrepresentableHom_refl (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] (R : CompleteLocalAlgCat Λ k) :
    fromProrepresentableHom p (Iso.refl (restrictedCoyoneda R)) = fromRestrictedHom p R :=
  sorry

end

end FormalObject

