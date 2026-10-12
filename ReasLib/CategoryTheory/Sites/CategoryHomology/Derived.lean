/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import ReasLib.CategoryTheory.Preadditive.Projective.Preserves
public import ReasLib.CategoryTheory.Limits.ChangeOfIndex
public import ReasLib.CategoryTheory.Sites.Presheaf.InverseImage
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived-colimit category homology

This leaf owns category homology as the left derived functors of colimit and its functorial maps.
It does not import the explicit bar construction; clients needing the comparison import
`CategoryHomology.Computation`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v u' v' u'' v'' w

namespace CategoryTheory.CategoryHomology

variable {C : Type u} [Category.{v} C]

section Basic

variable [HasColimitsOfShape Cᵒᵖ AddCommGrpCat.{w}]
variable [HasProjectiveResolutions (Cᵒᵖ ⥤ AddCommGrpCat.{w})]

/-- Example 21.39.1: category homology is the left-derived colimit of an additive presheaf. -/
@[stacks 08PF "category homology as a derived colimit"]
abbrev categoryHomology (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    AddCommGrpCat.{w} :=
  ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).leftDerived n).obj ℱ

/-- The degree-`n` derived-colimit homology functor in the coefficient presheaf. -/
@[stacks 08PF "derived category homology coefficient functor"]
noncomputable abbrev coefficientFunctor (n : ℕ) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w} :=
  (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).leftDerived n

/-- Derived-colimit category homology is additive in the coefficient presheaf. -/
@[stacks 08PF "additivity of derived category homology"]
instance coefficientFunctor.additive (n : ℕ) :
    (coefficientFunctor (C := C) n).Additive := sorry

/-- Evaluation of the derived-colimit coefficient functor on an object. -/
@[simp, stacks 08PF "derived category homology coefficient functor object formula"]
theorem coefficientFunctor_obj (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    (coefficientFunctor (C := C) n).obj ℱ = categoryHomology ℱ n := sorry

/-- Evaluation of the derived-colimit coefficient functor on a morphism. -/
@[simp, stacks 08PF "derived category homology coefficient functor map formula"]
theorem coefficientFunctor_map
    {ℱ ℱ' : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (t : ℱ ⟶ ℱ') (n : ℕ) :
    (coefficientFunctor (C := C) n).map t =
      ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).leftDerived n).map t := sorry

end Basic

section Functoriality

variable {C' : Type u'} [Category.{v'} C']

variable [HasColimitsOfShape Cᵒᵖ AddCommGrpCat.{w}]
variable [HasColimitsOfShape C'ᵒᵖ AddCommGrpCat.{w}]
variable [HasProjectiveResolutions (Cᵒᵖ ⥤ AddCommGrpCat.{w})]
variable [HasProjectiveResolutions (C'ᵒᵖ ⥤ AddCommGrpCat.{w})]

variable (u : C' ⥤ C)
variable [((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ
  AddCommGrpCat.{w}).obj u.op).PreservesProjectiveObjects]

/-- The canonical left-derived comparison for precomposition with `u.op`. -/
@[stacks 08PH "category homology precomposition left-derived comparison"]
noncomputable abbrev precompLeftDerivedIso
    (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    categoryHomology ((Functor.presheafInverseImage u AddCommGrpCat.{w}).obj ℱ) n ≅
      (((Functor.presheafInverseImage u AddCommGrpCat.{w}) ⋙
          (colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w})).leftDerived
        n).obj ℱ :=
  (((Functor.presheafInverseImage u AddCommGrpCat.{w}).mapProjectiveResolution
        (projectiveResolution ℱ)).isoLeftDerivedObj
      (colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}) n) ≪≫
    ((projectiveResolution ℱ).isoLeftDerivedObj
      ((Functor.presheafInverseImage u AddCommGrpCat.{w}) ⋙
        (colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w})) n).symm

/-- The derived-colimit map induced by a functor and a coefficient morphism. -/
@[stacks 08PH "category homology functorial map"]
abbrev map (u : C' ⥤ C)
    [((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ
      AddCommGrpCat.{w}).obj u.op).PreservesProjectiveObjects]
    {ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    {ℱ' : C'ᵒᵖ ⥤ AddCommGrpCat.{w}}
    (t : ℱ' ⟶ u.op ⋙ ℱ) (n : ℕ) :
    categoryHomology ℱ' n ⟶ categoryHomology ℱ n :=
  ((colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).leftDerived n).map t ≫
    (precompLeftDerivedIso u ℱ n).hom ≫
      (NatTrans.leftDerived (Limits.colimitPreNat u.op) n).app ℱ

end Functoriality

section Laws

variable [HasColimitsOfShape Cᵒᵖ AddCommGrpCat.{w}]
variable [HasProjectiveResolutions (Cᵒᵖ ⥤ AddCommGrpCat.{w})]

/-- The category-homology map attached to identities is the identity. -/
@[simp, stacks 08PH "category homology identity map"]
theorem map_id (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    map (C := C) (C' := C) (𝟭 C) (𝟙 ℱ) n = 𝟙 (categoryHomology ℱ n) := sorry

variable {C' : Type u'} [Category.{v'} C']
variable {C'' : Type u''} [Category.{v''} C'']
variable [HasColimitsOfShape C'ᵒᵖ AddCommGrpCat.{w}]
variable [HasColimitsOfShape C''ᵒᵖ AddCommGrpCat.{w}]
variable [HasProjectiveResolutions (C'ᵒᵖ ⥤ AddCommGrpCat.{w})]
variable [HasProjectiveResolutions (C''ᵒᵖ ⥤ AddCommGrpCat.{w})]

/-- Category-homology maps compose with indexing functors and coefficient morphisms. -/
@[simp, stacks 08PH "category homology map composition"]
theorem map_comp
    (u : C' ⥤ C) (v : C'' ⥤ C')
    [((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ AddCommGrpCat.{w}).obj
      u.op).PreservesProjectiveObjects]
    [((Functor.whiskeringLeft C''ᵒᵖ C'ᵒᵖ AddCommGrpCat.{w}).obj
      v.op).PreservesProjectiveObjects]
    {ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    {ℱ' : C'ᵒᵖ ⥤ AddCommGrpCat.{w}}
    {ℱ'' : C''ᵒᵖ ⥤ AddCommGrpCat.{w}}
    (t : ℱ' ⟶ u.op ⋙ ℱ) (s : ℱ'' ⟶ v.op ⋙ ℱ') (n : ℕ) :
    map (C := C) (C' := C'') (v ⋙ u)
        (s ≫ ((Functor.whiskeringLeft C''ᵒᵖ C'ᵒᵖ AddCommGrpCat.{w}).obj v.op).map t) n =
      map (C := C') (C' := C'') v s n ≫ map (C := C) (C' := C') u t n := sorry

end Laws

end CategoryTheory.CategoryHomology
