module

public import ReasLib.AlgebraicGeometry.ChowMotive.Representability
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Correspondence

universe u

variable {k : Type u} [Field k]

/- Lemma 45.5.2: the degree-`i` Chow-group functor on rational Chow motives is
 corepresented by the Tate-twisted unit, functorially in the motive. -/
@[stacks 0FGM] #check
  (ChowMotive.chowFunctorIsoCoyoneda (k := k) :
    ∀ i : ℤ,
      ChowMotive.chowFunctor (k := k) i ≅
        (linearCoyoneda ℚ
          (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k))).obj
          (Opposite.op
            (ChowMotive.tateTwist (SchemeOverField.point k) (-i))))

#check (ChowMotive.chowRepresentedBy (k := k) :
  ∀ i : ℤ,
    ((ChowMotive.chowFunctor (k := k) i) ⋙
      forget (ModuleCat.{u + 1} ℚ)).CorepresentableBy
      (ChowMotive.tateTwist (SchemeOverField.point k) (-i)))

#check (ChowMotive.chowGroupEquivHom (k := k) :
  ∀ (M : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) (i : ℤ),
    ChowMotive.chowGroup M i ≃ₗ[ℚ]
      (ChowMotive.tateTwist (SchemeOverField.point k) (-i) ⟶ M))
