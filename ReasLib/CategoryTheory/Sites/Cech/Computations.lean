module

public import ReasLib.CategoryTheory.Sites.Cech.Basic

/-!
# Computations for Čech complexes

This module records the canonical comparison of Mathlib's Čech complex with its formal-coproduct
and alternating-coface presentations. These formulas are coefficient-independent and are useful
whenever explicit Čech differentials are needed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

noncomputable section

universe w v v' u u'

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
variable {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]
variable {ι : Type w} (U : ι → C)

namespace AlgebraicTopology

/-- The differential in an alternating-coface complex is its canonical alternating coface map. -/
@[simp] theorem alternatingCofaceMapComplex_obj_d
    (X : CosimplicialObject A) (p : ℕ) :
    ((alternatingCofaceMapComplex A).obj X).d p (p + 1) =
      AlternatingCofaceMapComplex.objD X p := sorry

end AlgebraicTopology

/-- The Čech complex functor is the formal-coproduct cochain-complex functor for the Čech
simplicial formal coproduct of the family. -/
@[simp] theorem cechComplexFunctor_obj_eq_formalCoproductCochainComplex
    (F : Cᵒᵖ ⥤ A) :
    (cechComplexFunctor U).obj F =
      (FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk _ U).cech).obj F := sorry

/-- A formal-coproduct Čech cochain complex is the alternating-coface complex of its associated
Čech cosimplicial object. -/
@[simp] theorem formalCoproductCochainComplex_obj_eq_alternatingCofaceMapComplex_obj
    (F : Cᵒᵖ ⥤ A) :
    (FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk _ U).cech).obj F =
      (alternatingCofaceMapComplex A).obj
        ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F) := sorry

/-- The public Čech complex is the alternating-coface complex of the Čech cosimplicial object
attached to the formal coproduct of the family. -/
@[simp] theorem cechComplexFunctor_obj_eq_alternatingCofaceMapComplex_obj
    (F : Cᵒᵖ ⥤ A) :
    (cechComplexFunctor U).obj F =
      (alternatingCofaceMapComplex A).obj
        ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F) := sorry

/-- After identifying the whole Čech complex with its alternating-coface presentation, their
degree-`p` differentials agree. -/
@[simp] theorem cechComplexFunctor_obj_d_eq_alternatingCofaceMapComplex_obj_d
    (F : Cᵒᵖ ⥤ A) (p : ℕ) :
    ((cechComplexFunctor U).obj F).d p (p + 1) =
      ((alternatingCofaceMapComplex A).obj
        ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F)).d
        p (p + 1) := sorry

/-- The differential in the public Čech complex is definitionally the differential in its
formal-coproduct cochain-complex model. -/
@[simp] theorem cechComplexFunctor_obj_d_eq_formalCoproductCochainComplex_obj_d
    (F : Cᵒᵖ ⥤ A) (p : ℕ) :
    ((cechComplexFunctor U).obj F).d p (p + 1) =
      ((FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk _ U).cech).obj F).d
        p (p + 1) := sorry

/-- After identifying the formal-coproduct Čech cochain complex with its alternating-coface
presentation, their degree-`p` differentials agree. -/
@[simp] theorem formalCoproductCochainComplex_obj_d_eq_alternatingCofaceMapComplex_obj_d
    (F : Cᵒᵖ ⥤ A) (p : ℕ) :
    ((FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk _ U).cech).obj F).d p (p + 1) =
      ((alternatingCofaceMapComplex A).obj
        ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F)).d
        p (p + 1) := sorry

/-- The alternating-coface presentation of a formal-coproduct Čech object computes its
differential by `AlternatingCofaceMapComplex.objD`. -/
@[simp] theorem alternatingCofaceMapComplex_formalCoproduct_obj_d_eq_objD
    (F : Cᵒᵖ ⥤ A) (p : ℕ) :
    ((alternatingCofaceMapComplex A).obj
      ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F)).d
      p (p + 1) =
      AlternatingCofaceMapComplex.objD
        ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F) p := sorry

namespace CategoryTheory

variable {C₀ : Type u} [Category.{v} C₀]
variable {A₀ : Type u'} [Category.{v'} A₀] [HasProducts.{w} A₀] [Preadditive A₀]
variable (V : C₀) [HasFiniteProducts (Over V)]
variable {ι₀ : Type w}

/-- 21.8.0.1 (Tag 03AL): the differential of the public Cech complex is the alternating
coface operator on the Cech cosimplicial object of the family. The definition of
`AlternatingCofaceMapComplex.objD` is the signed sum of its coface maps. -/
@[stacks 03AL, simp] theorem cechComplex_d_eq_objD
    (family : ι₀ → Over V) (F : C₀ᵒᵖ ⥤ A₀) (p : ℕ) :
    (cechComplex V family F).d p (p + 1) =
      AlternatingCofaceMapComplex.objD
        ((FormalCoproduct.cosimplicialObjectFunctor
          (FormalCoproduct.mk _ family).cech).obj
          ((restrictPresheafToOver V).obj F)) p := sorry

end CategoryTheory

/-- The differential in the formal-coproduct Čech cochain complex is its alternating coface
operator. -/
theorem formalCoproductCochainComplex_obj_d_eq_objD
    (F : Cᵒᵖ ⥤ A) (p : ℕ) :
    ((FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk _ U).cech).obj F).d p (p + 1) =
      AlternatingCofaceMapComplex.objD
        ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F) p := sorry

/-- The degree-`p` differential in the Čech complex is the alternating coface operator of its
formal-coproduct Čech cosimplicial object. -/
@[simp] theorem cechComplexFunctor_obj_d_eq_objD
    (F : Cᵒᵖ ⥤ A) (p : ℕ) :
    ((cechComplexFunctor U).obj F).d p (p + 1) =
      AlternatingCofaceMapComplex.objD
        ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F) p := sorry

/-- 20.9.0.1 (Tag 01EE): the source-facing Čech differential computation, stated at the
canonical Čech functor. -/
@[stacks 01EE, simp] theorem cechComplexFunctor_d_eq_objD
    (F : Cᵒᵖ ⥤ A) (p : ℕ) :
    ((cechComplexFunctor U).obj F).d p (p + 1) =
      AlternatingCofaceMapComplex.objD
        ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F) p := sorry
