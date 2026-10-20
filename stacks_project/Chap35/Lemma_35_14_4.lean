module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Descent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Descent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 35.14.4 (1): in a commutative triangle `f ≫ q = p`, syntomicity descends
from `p` to `q` along a surjective syntomic morphism `f`. -/
@[stacks 02KM] #check
  (AlgebraicGeometry.Syntomic.of_comp_eq_of_surjective :
    ∀ {X Y S : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ S)
      [Surjective f] [Syntomic f] [Syntomic p] (_ : f ≫ q = p), Syntomic q)

/- Lemma 35.14.4 (2): in a commutative triangle `f ≫ q = p`, smoothness descends
from `p` to `q` along a surjective smooth morphism `f`. -/
@[stacks 02KM] #check
  (AlgebraicGeometry.Smooth.of_comp_eq_of_surjective :
    ∀ {X Y S : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ S)
      [Surjective f] [Smooth f] [Smooth p] (_ : f ≫ q = p), Smooth q)

/- Lemma 35.14.4 (3): in a commutative triangle `f ≫ q = p`, étaleness descends
from `p` to `q` along a surjective étale morphism `f`. -/
@[stacks 02KM] #check
  (AlgebraicGeometry.Etale.of_comp_eq_of_surjective :
    ∀ {X Y S : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ S)
      [Surjective f] [Etale f] [Etale p] (_ : f ≫ q = p), Etale q)
