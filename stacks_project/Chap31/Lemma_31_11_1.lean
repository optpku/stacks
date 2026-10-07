module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Torsion

open AlgebraicGeometry
open Opposite
open scoped AlgebraicGeometry

universe u

/- Lemma 31.11.1: for a section of a quasi-coherent module on a nonempty open of an integral
scheme, having a torsion germ somewhere, having torsion germs everywhere, vanishing in the
generic stalk, and vanishing in the generic-point skyscraper pushforward are equivalent. -/
@[stacks 0AXR] #check
  (AlgebraicGeometry.Scheme.Modules.SectionTorsion.tfae :
    ∀ {X : Scheme.{u}} [IsIntegral X]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      {U : X.Opens} (hU : Set.Nonempty (U : Set X)) (s : ℱ.val.obj (op U)),
      List.TFAE [
        ∃ x : U, AlgebraicGeometry.Scheme.Modules.SectionTorsion.IsAt ℱ s x,
        ∀ x : U, AlgebraicGeometry.Scheme.Modules.SectionTorsion.IsAt ℱ s x,
        AlgebraicGeometry.Scheme.Modules.SectionTorsion.genericGerm ℱ hU s = 0,
        AlgebraicGeometry.Scheme.Modules.SectionTorsion.genericSkyscraperImage ℱ s = 0])
