module

public import stacks_project.Chap61.Lemma_61_12_15_Big
public import stacks_project.Chap61.Lemma_61_12_16_Comparison

/-!
# Composition of pro-étale morphisms of topoi

This leaf owns the composition laws for the big and small pro-étale morphisms
of topoi attached to a pair of composable carrier morphisms in a chosen big
pro-étale presentation.
-/

@[expose] public section

open CategoryTheory
open scoped MorphismOfTopoiIn

noncomputable section

universe u v w

namespace AlgebraicGeometry.ChosenBigProetaleSite
namespace Big

/-- Big pro-étale morphisms of topoi compose along composition of morphisms in a
chosen big pro-étale presentation. -/
theorem morphismOfTopoi_comp {X : ChosenBigProetaleSite.{u, v}}
    {R S T : X.carrier} (f : R ⟶ S) (g : S ⟶ T) :
    MorphismOfTopoiIn.comp (morphismOfTopoi g) (morphismOfTopoi f) =
      morphismOfTopoi (f ≫ g) := sorry

end Big

namespace SmallToBig

/-- Small pro-étale morphisms of topoi compose along composition of morphisms in
a chosen big pro-étale presentation. -/
theorem smallMorphism_comp {X : ChosenBigProetaleSite.{u, v}}
    {R S T : X.carrier} (f : R ⟶ S) (g : S ⟶ T) :
    MorphismOfTopoiIn.comp (smallMorphism g) (smallMorphism f) =
      smallMorphism (f ≫ g) := sorry

end SmallToBig
end AlgebraicGeometry.ChosenBigProetaleSite
