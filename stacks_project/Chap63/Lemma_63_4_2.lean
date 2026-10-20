module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.Stalk
public import stacks_project.Chap63.Lemma_63_4_2_StalkCoproduct
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint AlgebraicGeometry.Scheme.Etale

universe u

/- Lemma 63.4.2. For a locally quasi-finite morphism, the finite-support presheaf
stalk is functorially the coproduct of the stalks at the same-field geometric lifts. -/
@[stacks 0F6P] #check (AlgebraicGeometry.Scheme.Etale.lowerShriekPresheafStalkIso :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
    (ybar : GeometricPoint Y),
    lowerShriekPresheaf f ⋙ (toSmallEtalePoint ybar).presheafFiber ≅
      abelianStalkCoproduct f ybar)
