/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowMotive.Representability
public import ReasLib.AlgebraicGeometry.Correspondence.TateGraded
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Correspondence

universe u

variable {k : Type u} [Field k]

/- Lemma 45.5.2:
the degree-`i` Chow group of a rational Chow motive is naturally equivalent to morphisms from the Tate-twisted unit in degree `-i`, functorially in the motive. -/
@[stacks 0FGM] #check
  (ChowMotive.chowRepresentedBy (k := k) (C := Correspondence.TateGraded k)
    (fun n ↦ Correspondence.TateGraded.ofScheme (SchemeOverField.point k) n) :
    ∀ i : ℤ,
      Nonempty
        (((ChowMotive.chowFunctor (k := k)
            (GradedCorrespondence := fun _ ↦ Correspondence.TateGraded k)
            (fun j ↦ (linearCoyoneda ℚ (Correspondence.TateGraded k)).obj
              (Opposite.op (Correspondence.TateGraded.ofScheme
                (SchemeOverField.point k) (-j)))) i) ⋙ forget (ModuleCat.{u + 1} ℚ)).CorepresentableBy
          (Correspondence.TateGraded.ofScheme (SchemeOverField.point k) (-i) :
            ChowMotive k (fun _ ↦ Correspondence.TateGraded k))))

/- Objectwise form of the Chow-group representability equivalence. -/
#check (ChowMotive.chowGroup_equiv_hom (k := k)
    (fun n ↦ Correspondence.TateGraded.ofScheme (SchemeOverField.point k) n)
    : ∀ (M : ChowMotive k (fun _ ↦ Correspondence.TateGraded k)) (i : ℤ),
      Nonempty
        (ChowMotive.chowGroup (k := k)
            (GradedCorrespondence := fun _ ↦ Correspondence.TateGraded k)
            (fun n ↦ (linearCoyoneda ℚ (Correspondence.TateGraded k)).obj
              (Opposite.op (Correspondence.TateGraded.ofScheme
                (SchemeOverField.point k) (-n)))) M i ≃
          ((Correspondence.TateGraded.ofScheme
              (SchemeOverField.point k) (-i) :
              ChowMotive k (fun _ ↦ Correspondence.TateGraded k)) ⟶ M)))
