module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Pullback
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace DescentData
namespace Pullback

variable {X X' S : Scheme.{u}}

/- Lemma 35.35.6: morphisms in both directions between schemes over `S` induce an
equivalence between their categories of descent data, whose forward functor is pullback. -/
@[stacks 0243] #check (AlgebraicGeometry.Scheme.DescentData.Pullback.equivalence :
  (a : X ⟶ S) → (a' : X' ⟶ S) → (f : X' ⟶ X) →
    CommSq f a' a (𝟙 S) → (g : X ⟶ X') → CommSq g a a' (𝟙 S) →
      (DescentData (fun _ : PUnit.{1} ↦ X) (fun _ : PUnit.{1} ↦ a) ≌
        DescentData (fun _ : PUnit.{1} ↦ X') (fun _ : PUnit.{1} ↦ a')))

#check (AlgebraicGeometry.Scheme.DescentData.Pullback.equivalence_functor :
  ∀ (a : X ⟶ S) (a' : X' ⟶ S) (f : X' ⟶ X)
    (sqf : CommSq f a' a (𝟙 S)) (g : X ⟶ X') (sqg : CommSq g a a' (𝟙 S)),
    (equivalence a a' f sqf g sqg).functor = functor a a' (𝟙 S) f sqf)

#check (AlgebraicGeometry.Scheme.DescentData.Pullback.equivalence_inverse :
  ∀ (a : X ⟶ S) (a' : X' ⟶ S) (f : X' ⟶ X)
    (sqf : CommSq f a' a (𝟙 S)) (g : X ⟶ X') (sqg : CommSq g a a' (𝟙 S)),
    (equivalence a a' f sqf g sqg).inverse = functor a' a (𝟙 S) g sqg)

end Pullback
end DescentData
end Scheme
end AlgebraicGeometry
