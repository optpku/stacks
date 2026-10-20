module

public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.Smooth
import StacksCheckRecall

/-!
# Étale morphisms of algebraic spaces are smooth
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.39.6: An étale morphism of algebraic spaces is smooth. -/
@[stacks 04XX] #check (AlgebraicGeometry.AlgebraicSpace.smooth_of_etale :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f], Smooth f)

end AlgebraicGeometry.AlgebraicSpace
