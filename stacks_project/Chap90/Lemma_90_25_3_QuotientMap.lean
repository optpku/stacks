/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import stacks_project.Chap90.Definition_90_25_1_Quotient
public import stacks_project.Chap90.Lemma_90_25_2
public import stacks_project.Chap90.Lemma_90_25_2_Pullback

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

/-- The action of `[f]` on a Grothendieck arrow: the image of the unique elements-arrow
over the base morphism, followed by the inverse of the kernel-pair isomorphism. -/
def quotientMapHom (f : Functor.ofTypeValued U ⟶ F)
    {p q : (ofMorphism f).quotient.total} (φ : p ⟶ q) :
    imageObj f p.base p.fiber ⟶ imageObj f q.base q.fiber :=
  let a : PointHom (ofMorphism f) q.base ((ofMorphism f).U.map φ.base p.fiber) q.fiber :=
    φ.fiber
  imageLift f φ.base p.fiber ≫
    eqToHom (congrArg (imageObj f q.base) a.source.symm) ≫
    a.arrow.inv ≫
    eqToHom (congrArg (imageObj f q.base) a.target)

/-- The total functor underlying `[f] : [U/R] ⟶ F`. -/
def quotientMapFunctor (f : Functor.ofTypeValued U ⟶ F) :
    (ofMorphism f).quotient.total ⥤ F.total where
  obj p := imageObj f p.base p.fiber
  map φ := quotientMapHom f φ
  map_id := sorry
  map_comp := sorry

/-- The canonical morphism `[f] : [U/R] ⟶ F` of categories over `C` associated to a
morphism `f : U ⟶ F` of categories cofibered in groupoids, with kernel-pair groupoid
`ofMorphism f`. -/
def quotientMap (f : Functor.ofTypeValued U ⟶ F) :
    (ofMorphism f).quotient.toBasedCategory ⥤ᵇ F.toBasedCategory where
  toFunctor := quotientMapFunctor f
  w := sorry

/-- On objects, `[f]` sends `(T, x)` to the image of `x` under `f`. -/
theorem quotientMap_obj (f : Functor.ofTypeValued U ⟶ F) (T : C) (x : U.obj T) :
    (quotientMap f).obj ⟨T, x⟩ = imageObj f T x := sorry

/-- The canonical morphism `[f]` is full. -/
instance quotientMap_full (f : Functor.ofTypeValued U ⟶ F) :
    (quotientMap f).Full := sorry

/-- The canonical morphism `[f]` is faithful. -/
instance quotientMap_faithful (f : Functor.ofTypeValued U ⟶ F) :
    (quotientMap f).Faithful := sorry

/-- The canonical morphism `[f]` is an equivalence of categories over `C` whenever `f`
is essentially surjective. -/
instance quotientMap_isEquivalence (f : Functor.ofTypeValued U ⟶ F)
    [(CofiberedCategoryOver.Groupoids.toBasedFunctor f).EssSurj] :
    BasedFunctor.IsEquivalence (quotientMap f) := sorry

end CategoryTheory.GroupoidInFunctors
