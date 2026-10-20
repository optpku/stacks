module

public import ReasLib.AlgebraicTopology.SimplicialObject.Skeleton.Counit.Abelian
public import ReasLib.AlgebraicTopology.SimplicialObject.Skeleton.Tower.Mono
public import ReasLib.AlgebraicTopology.SimplicialObject.Skeleton.Tower.Colimit
import StacksCheckRecall

/-!
@stack 0193

# Source-facing recall for Lemma 14.22.5

The canonical skeleton tower of a simplicial object in an abelian category has monomorphic
transitions and colimit the original simplicial object.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.Skeleton

variable {A : Type u} [Category.{v} A] [Abelian A]

variable (V : SimplicialObject A)

#check (fun n ↦ succMap V n :
  (n : ℕ) → (sk n).obj V ⟶ (sk (n + 1)).obj V)

#check (sequence V : ℕ ⥤ SimplicialObject A)

#check (cocone V : Cocone (sequence V))

#check (fun n ↦ Tower.step (A := A) n :
  (n : ℕ) → sk n ⟶ sk (n + 1))

#check (Tower.diagram (A := A) :
  ℕ ⥤ (SimplicialObject A ⥤ SimplicialObject A))

#check (Tower.cocone (A := A) : Cocone (Tower.diagram (A := A)))

#check (evaluation.isEventuallyConstantFrom V :
  (Δ : SimplexCategoryᵒᵖ) →
    Functor.IsEventuallyConstantFrom
      (sequence V ⋙ (evaluation _ A).obj Δ) Δ.unop.len)

/- Lemma 14.22.5 (1): `V` is the colimit of its canonical skeleton tower. -/
@[stacks 0193]
#check (isColimit V : IsColimit (cocone V))

#check (Tower.isColimit (A := A) : IsColimit (Tower.cocone (A := A)))

/- Lemma 14.22.5 (2): every transition in the skeleton tower is monomorphic. -/
@[stacks 0193]
#check (inferInstance :
  ∀ {i j : ℕ} (f : i ⟶ j), Mono ((sequence V).map f))

#check (inferInstance : ∀ n : ℕ, Mono (Tower.step (A := A) n))

#check (inferInstance : ∀ {i j : ℕ} (f : i ⟶ j),
  Mono ((Tower.diagram (A := A)).map f))

end CategoryTheory.SimplicialObject.Skeleton
