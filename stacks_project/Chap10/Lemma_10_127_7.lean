/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.FinitePresentation
public import ReasLib.RingTheory.Algebra.TensorProduct.Map
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.RingTheory.DirectLimit.Algebra.Tensor
public import ReasLib.RingTheory.DirectLimit.Algebra.BaseChange.FiniteType
public import ReasLib.RingTheory.DirectLimit.Algebra.BaseChange.FinitePresentation

/-!
# Descent from filtered colimits

@stack 05N8

The neutral direct-limit layer owns stage tensor maps and finite-type or finite-presentation
descent.  This file retains the source-facing `CommAlgCat` formulation of the four clauses.
-/

@[expose] public section

open CategoryTheory Limits
open scoped TensorProduct Algebra.TensorProduct.Right

universe u v

section

variable {A : Type u} [CommRing A]
variable {B C : Type u} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]

#check @Ring.DirectLimit.stageTensorMap
#check @Ring.DirectLimit.Algebra.BaseChange.FiniteType.exists_surjective
#check @Ring.DirectLimit.BaseChange.FinitePresentation.exists_stageMap

/-- Lemma 10.127.7 (Tag 05N8) (1): if `B` is finite type over `A` and two
`A`-algebra maps `u, u' : B →ₐ[A] C` agree after tensoring with a filtered
colimit, they agree after tensoring with some stage. -/
@[stacks 05N8 "(1)"]
theorem finite_type_map_equality_descends
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} A) [HasColimit F]
    [Algebra.FiniteType A B]
    (u u' : B →ₐ[A] C)
    (h :
      Algebra.TensorProduct.map u
          (AlgHom.id A (((colimit F : CommAlgCat A) : Type u))) =
        Algebra.TensorProduct.map u'
          (AlgHom.id A (((colimit F : CommAlgCat A) : Type u)))) :
    ∃ j : J,
      Algebra.TensorProduct.map u
          (AlgHom.id A (((F.obj j : CommAlgCat A) : Type u))) =
        Algebra.TensorProduct.map u'
          (AlgHom.id A (((F.obj j : CommAlgCat A) : Type u))) := sorry

/-- Lemma 10.127.7 (Tag 05N8) (2): if `C` is finite type over `A` and the
base change of `u : B →ₐ[A] C` to the filtered colimit is surjective, it is
surjective after tensoring with some stage. -/
@[stacks 05N8 "(2)"]
theorem finite_type_surjectivity_descends
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} A) [HasColimit F]
    [Algebra.FiniteType A C]
    (u : B →ₐ[A] C)
    (h :
      Function.Surjective
        (Algebra.TensorProduct.map u
          (AlgHom.id A (((colimit F : CommAlgCat A) : Type u))))) :
    ∃ j : J,
      Function.Surjective
        (Algebra.TensorProduct.map u
          (AlgHom.id A (((F.obj j : CommAlgCat A) : Type u)))) := sorry

/-- Lemma 10.127.7 (Tag 05N8) (3): every algebra map from the tensor
base change of a finitely presented `C` to the tensor base change of `B`
descends to an algebra map at some stage. -/
@[stacks 05N8 "(3)"]
theorem finite_presentation_hom_descends
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} A) [HasColimit F]
    [Algebra.FinitePresentation A C]
    (v :
      C ⊗[A] ((colimit F : CommAlgCat A) : Type u) →ₐ[((colimit F : CommAlgCat A) : Type u)]
        B ⊗[A] ((colimit F : CommAlgCat A) : Type u)) :
    ∃ (j : J)
        (v_j :
          C ⊗[A] ((F.obj j : CommAlgCat A) : Type u) →ₐ[((F.obj j : CommAlgCat A) : Type u)]
            B ⊗[A] ((F.obj j : CommAlgCat A) : Type u)),
        (Algebra.TensorProduct.map (AlgHom.id A B) (colimit.ι F j).hom).comp
            (v_j.restrictScalars A) =
          (v.restrictScalars A).comp
            (Algebra.TensorProduct.map (AlgHom.id A C) (colimit.ι F j).hom) := sorry

/-- Lemma 10.127.7 (Tag 05N8) (4): if `B` is finite type, `C` is finitely
presented, and the colimit base change of `u` is bijective, then its base
change is bijective at some stage. -/
@[stacks 05N8 "(4)"]
theorem finite_type_finite_presentation_bijective_descends
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} A) [HasColimit F]
    [Algebra.FiniteType A B] [Algebra.FinitePresentation A C]
    (u : B →ₐ[A] C)
    (h :
      Function.Bijective
        (Algebra.TensorProduct.map u
          (AlgHom.id A (((colimit F : CommAlgCat A) : Type u))))) :
    ∃ j : J,
      Function.Bijective
        (Algebra.TensorProduct.map u
          (AlgHom.id A (((F.obj j : CommAlgCat A) : Type u)))) := sorry

end

#check @finite_type_map_equality_descends
#check @finite_type_surjectivity_descends
#check @finite_presentation_hom_descends
#check @finite_type_finite_presentation_bijective_descends
