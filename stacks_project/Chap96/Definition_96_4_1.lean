module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Topology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Definition 96.4.1 (1): the associated Zariski site `X.zariskiTopology` is the
structure of site on `X` inherited from `(Sch/S)_Zar`. -/
@[stacks 06TP] #check (AlgebraicGeometry.GroupoidsOver.zariskiTopology :
  ∀ {S : Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S), GrothendieckTopology X.total)

/- Definition 96.4.1 (2): the associated étale site `X.etaleTopology` is the
structure of site on `X` inherited from `(Sch/S)_étale`. -/
@[stacks 06TP] #check (AlgebraicGeometry.GroupoidsOver.etaleTopology :
  ∀ {S : Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S), GrothendieckTopology X.total)

/- Definition 96.4.1 (3): the associated smooth site `X.smoothTopology` is the
structure of site on `X` inherited from `(Sch/S)_smooth`. -/
@[stacks 06TP] #check (AlgebraicGeometry.GroupoidsOver.smoothTopology :
  ∀ {S : Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S), GrothendieckTopology X.total)

/- Definition 96.4.1 (4): the associated syntomic site `X.syntomicTopology` is the
structure of site on `X` inherited from `(Sch/S)_syntomic`. -/
@[stacks 06TP] #check (AlgebraicGeometry.GroupoidsOver.syntomicTopology :
  ∀ {S : Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S), GrothendieckTopology X.total)

/- Definition 96.4.1 (5): the associated fppf site `X.fppfTopology` is the
structure of site on `X` inherited from `(Sch/S)_fppf`. -/
@[stacks 06TP] #check (AlgebraicGeometry.GroupoidsOver.fppfTopology :
  ∀ {S : Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S), GrothendieckTopology X.total)
