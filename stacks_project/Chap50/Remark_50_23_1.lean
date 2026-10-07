module

import StacksCheckRecall
import stacks_project.Chap50.«50_23_1_1_Gysin»

open AlgebraicGeometry CategoryTheory

universe u

/- Remark 50.23.1: The degree-`p` Gysin morphism associated to an ordered family of
equations is obtained from an ambient lift by taking its local-cohomology class and
wedging with the ordered equation differentials. -/
@[stacks 0G83] #check (@AlgebraicGeometry.Scheme.DeRham.Gysin.map :
  {X S : Scheme.{u}} → (q : X ⟶ S) → {c : ℕ} → (fs : Fin c → Γ(X, ⊤)) → (p : ℕ) →
    AlgebraicGeometry.Scheme.DeRham.Gysin.source q fs p ⟶
      (ModuleCech.LocalCohomology.cohomologyFunctor fs).obj
        (AlgebraicGeometry.Scheme.DeRham.Gysin.relativeForm q (p + c)))

/- The formula for the Gysin morphism after the canonical quotient projection. -/
#check @AlgebraicGeometry.Scheme.DeRham.Gysin.projection_map

/- The pre-Gysin morphism annihilates the differential-form relations. -/
#check @AlgebraicGeometry.Scheme.DeRham.Gysin.relationMap_preMap
