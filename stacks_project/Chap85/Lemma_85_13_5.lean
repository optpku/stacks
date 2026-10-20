module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Definition_85_12_1_Cartesian

/-!
# Lemma 85.13.5

In Situation 85.3.3, a map of objects of `D(C_total)` out of a cartesian object
is zero once it vanishes in degree `0` and the indicated stage Hom-groups vanish.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instMorphismDiagram : IsMorphismDiagram C J]
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
include instMorphismDiagram instWeakSheafify instLeftKan
variable [UnivLE.{max u v, w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

/-- Lemma 85.13.5
In Situation 85.3.3, let `K, K'` be objects of `D(C_total)` with `K` cartesian.
If `Hom(K_i⟦i⟧, K'_i) = 0` for `i > 0` and `Hom(K_i⟦i + 1⟧, K'_i) = 0` for
`i ≥ 0`, then any map `K ⟶ K'` inducing the zero map `K_0 ⟶ K'_0` is zero. -/
@[stacks 0D9J]
theorem cartesianDerived_hom_eq_zero
    (K K' : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    [Derived.IsCartesian C J K]
    (h_hom : ∀ n : SimplexCategory, 0 < n.len →
      Subsingleton (((derivedComponent C J n).obj K)⟦(n.len : ℤ)⟧ ⟶
        (derivedComponent C J n).obj K'))
    (h_hom_succ : ∀ n : SimplexCategory,
      Subsingleton (((derivedComponent C J n).obj K)⟦(n.len + 1 : ℤ)⟧ ⟶
        (derivedComponent C J n).obj K'))
    (f : K ⟶ K') (hf0 : (derivedComponent C J ⦋0⦌).map f = 0) :
    f = 0 :=
  sorry

/-- Maps `K ⟶ K'` out of a cartesian object of `D(C_total)` that agree on the
degree-`0` component are equal, under the stage Hom-vanishing hypotheses of
`cartesianDerived_hom_eq_zero`. -/
theorem cartesianDerived_hom_eq_of_eq_component
    (K K' : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    [Derived.IsCartesian C J K]
    (h_hom : ∀ n : SimplexCategory, 0 < n.len →
      Subsingleton (((derivedComponent C J n).obj K)⟦(n.len : ℤ)⟧ ⟶
        (derivedComponent C J n).obj K'))
    (h_hom_succ : ∀ n : SimplexCategory,
      Subsingleton (((derivedComponent C J n).obj K)⟦(n.len + 1 : ℤ)⟧ ⟶
        (derivedComponent C J n).obj K'))
    (f g : K ⟶ K')
    (hfg : (derivedComponent C J ⦋0⦌).map f = (derivedComponent C J ⦋0⦌).map g) :
    f = g :=
  sorry

end CategoryTheory.SimplicialSites
