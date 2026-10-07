module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.WeaklyEtale.Criteria
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 37.64.9 (1): a flat monomorphism of schemes is weakly étale. -/
@[stacks 094X] #check
  (AlgebraicGeometry.WeaklyEtale.instOfFlatOfMono :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Mono f], WeaklyEtale f)

/- Lemma 37.64.9 (2): an open immersion of schemes is weakly étale. -/
@[stacks 094X] #check
  (AlgebraicGeometry.WeaklyEtale.of_isOpenImmersion :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f], WeaklyEtale f)

/- Lemma 37.64.9 (3): a flat unramified morphism of schemes is weakly étale. -/
@[stacks 094X] #check
  (AlgebraicGeometry.WeaklyEtale.instOfFlatOfUnramified :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Unramified f], WeaklyEtale f)

/- Lemma 37.64.9 (4): an étale morphism of schemes is weakly étale. -/
@[stacks 094X] #check
  (AlgebraicGeometry.WeaklyEtale.of_etale :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f], WeaklyEtale f)
