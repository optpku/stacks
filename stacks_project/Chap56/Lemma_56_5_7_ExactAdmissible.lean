module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import stacks_project.Chap56.Lemma_56_5_2_Admissible

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.QCoh

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}

/-- An admissible functor of quasicoherent modules is exact-admissible when it is
an exact functor `Scheme.QCoh X ⥤ Scheme.QCoh Y`. -/
class ExactAdmissible (x : X ⟶ Spec (CommRingCat.of R))
    (y : Y ⟶ Spec (CommRingCat.of R)) (F : Scheme.QCoh X ⥤ Scheme.QCoh Y) : Prop
    extends Admissible x y F where
  exact : exactFunctor (Scheme.QCoh X) (Scheme.QCoh Y) F

/-- Exact-admissibility is equivalent to admissibility together with exactness. -/
theorem exactAdmissible_iff (x : X ⟶ Spec (CommRingCat.of R))
    (y : Y ⟶ Spec (CommRingCat.of R)) (F : Scheme.QCoh X ⥤ Scheme.QCoh Y) :
    ExactAdmissible x y F ↔
      Admissible x y F ∧ exactFunctor (Scheme.QCoh X) (Scheme.QCoh Y) F := sorry

/-- The category of `R`-linear exact functors `Scheme.QCoh X ⥤ Scheme.QCoh Y`
that preserve arbitrary coproducts. -/
abbrev ExactCoproductLinearFunctor (x : X ⟶ Spec (CommRingCat.of R))
    (y : Y ⟶ Spec (CommRingCat.of R)) :=
  ObjectProperty.FullSubcategory
    fun F : Scheme.QCoh X ⥤ Scheme.QCoh Y ↦ ExactAdmissible x y F

/-- Objects of `ExactCoproductLinearFunctor` are exact-admissible functors. -/
theorem exactCoproductLinearFunctor_property (x : X ⟶ Spec (CommRingCat.of R))
    (y : Y ⟶ Spec (CommRingCat.of R))
    (F : ExactCoproductLinearFunctor x y) :
    ExactAdmissible x y F.obj := F.property

end AlgebraicGeometry.Scheme.QCoh
