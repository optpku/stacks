/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.BaseChange
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Pi.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {ι : Type u}
variable (A : ι → Type u) [∀ i, CommRing (A i)]
variable {𝓖 : Type v} [Category.{w} 𝓖] [HasZeroMorphisms 𝓖] [HasKernels 𝓖]
variable {𝓕 : ι → Type v} [∀ i, Category.{w} (𝓕 i)]
  [∀ i, HasZeroMorphisms (𝓕 i)] [∀ i, HasKernels (𝓕 i)]

variable (e : 𝓖 ≌ ((i : ι) → 𝓕 i))
variable (modules : ModuleCat.{u} (∀ i, A i) ≌ ((i : ι) → ModuleCat.{u} (A i)))
variable (underline : ModuleCat.{u} (∀ i, A i) ⥤ 𝓖)
variable (underlines : (i : ι) → ModuleCat.{u} (A i) ⥤ 𝓕 i)
variable (compatibility : underline ⋙ e.functor ≅ modules.functor ⋙ Functor.pi underlines)

include modules compatibility in
/-- Adequacy over a product is equivalent to componentwise adequacy under a compatible
decomposition of the ambient categories. -/
theorem Adequate.pi_iff_of_compatible (F : 𝓖) :
    Adequate (∀ i, A i) underline F ↔
      ∀ i, Adequate (A i) (underlines i) ((e.functor.obj F) i) := sorry

/-- Adequacy is invariant under isomorphisms in a category with kernels. -/
instance Adequate.isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun F : 𝓖 ↦ Adequate (∀ i, A i) underline F) := sorry

/-- Componentwise adequacy is invariant under isomorphisms. -/
instance Adequate.piIsClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun F : (i : ι) → 𝓕 i ↦
        ∀ i, Adequate (A i) (underlines i) (F i)) := sorry

include modules compatibility in
/-- The componentwise adequate property is the inverse image of adequacy under the compatible
equivalence. -/
theorem Adequate.piInverseImage :
    ObjectProperty.inverseImage
      (fun F : (i : ι) → 𝓕 i ↦
        ∀ i, Adequate (A i) (underlines i) (F i)) e.functor =
      (fun F : 𝓖 ↦ Adequate (∀ i, A i) underline F) := sorry

include e modules compatibility in
/-- A compatible ambient equivalence restricts to an equivalence on adequate objects. -/
noncomputable def Adequate.piEquivalenceOfCompatible :
    ObjectProperty.FullSubcategory
        (fun F : 𝓖 ↦ Adequate (∀ i, A i) underline F) ≌
      ObjectProperty.FullSubcategory
        (fun F : (i : ι) → 𝓕 i ↦
          ∀ i, Adequate (A i) (underlines i) (F i)) :=
  e.congrFullSubcategory
    (Adequate.piInverseImage A e modules underline underlines compatibility)

/-- The restricted compatible equivalence acts on objects through the ambient equivalence. -/
theorem Adequate.piEquivalenceOfCompatible_obj
    (F : ObjectProperty.FullSubcategory
      (fun F : 𝓖 ↦ Adequate (∀ i, A i) underline F)) :
    ((Adequate.piEquivalenceOfCompatible A e modules underline underlines compatibility).functor.obj
      F).obj = e.functor.obj F.obj := sorry

namespace ModuleValuedFunctor

/-- Restricting a tensor-adequate module-valued functor over a product to a factor
preserves tensor adequacy. -/
theorem TensorAdequate.restrictPi (i : ι)
    (F : ObjectProperty.FullSubcategory
      (TensorAdequate (A := CommRingCat.of (∀ i, A i)))) :
    TensorAdequate (A := CommRingCat.of (A i))
      ((restrictAlong (CommRingCat.ofHom (Pi.evalRingHom A i))).obj F.obj) := sorry

/-- The canonical restriction functor from tensor-adequate functors over a product to the
family of tensor-adequate functors over its factors. -/
noncomputable def adequateFunctorPi :
    ObjectProperty.FullSubcategory
        (TensorAdequate (A := CommRingCat.of (∀ i, A i))) ⥤
      ((i : ι) → ObjectProperty.FullSubcategory
        (TensorAdequate (A := CommRingCat.of (A i)))) :=
  Functor.pi' fun i ↦
    ObjectProperty.lift
      (TensorAdequate (A := CommRingCat.of (A i)))
      (ObjectProperty.ι (TensorAdequate (A := CommRingCat.of (∀ i, A i))) ⋙
        restrictAlong (CommRingCat.ofHom (Pi.evalRingHom A i)))
      (TensorAdequate.restrictPi A i)

/-- The canonical finite-product restriction functor is an equivalence. -/
theorem adequateFunctorPiIsEquivalence [Finite ι] :
    (adequateFunctorPi A).IsEquivalence := sorry

end ModuleValuedFunctor
