module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.FreeLocus

open CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

/- Lemma 37.16.8 (1): the free-neighborhood locus is open. -/
@[stacks 0CZR] #check (AlgebraicGeometry.Scheme.Modules.isOpen_freeLocus_of_flatOver :
  {X S : AlgebraicGeometry.Scheme.{u}} → (f : X ⟶ S) →
  [AlgebraicGeometry.LocallyOfFinitePresentation f] →
  (F : X.Modules) → [F.IsFinitePresentation] → AlgebraicGeometry.Scheme.Modules.flatOver F f →
  IsOpen (AlgebraicGeometry.Scheme.Modules.freeLocus F : Set X))

/- Lemma 37.16.8 (2): the free-neighborhood locus commutes with arbitrary base change. -/
@[stacks 0CZR] #check (AlgebraicGeometry.Scheme.Modules.freeLocus_baseChange :
  {X S S' : AlgebraicGeometry.Scheme.{u}} → (f : X ⟶ S) →
  [AlgebraicGeometry.LocallyOfFinitePresentation f] →
  (F : X.Modules) → [F.IsFinitePresentation] → (h : AlgebraicGeometry.Scheme.Modules.flatOver F f) →
  (g : S' ⟶ S) → AlgebraicGeometry.Scheme.Modules.freeLocus (AlgebraicGeometry.Scheme.Modules.baseChangeModule f g F) =
    (Opens.map (pullback.fst f g).base).obj (AlgebraicGeometry.Scheme.Modules.freeLocus F))
