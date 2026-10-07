module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Fiber

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 29.36.8: a flat, locally finitely presented morphism whose residue-field fibres are
coproducts of spectra of finite separable field extensions is étale. -/
@[stacks 02GM] #check
  (AlgebraicGeometry.Scheme.Hom.etale_of_flat_of_finiteSeparableFibers :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f],
      f.FibersAreDisjointUnionOfSpecFiniteSeparable → Etale f)
