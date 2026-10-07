module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.NonzeroSheaf
import StacksCheckRecall

/-!
# A nonzero étale sheaf vanishing on fields and invariant under thickenings
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

/- Lemma 110.58.1: there exists a sheaf of abelian groups `G` on the big
étale site such that `G` vanishes on spectra of fields, is limit preserving,
restriction along every thickening is an isomorphism, and `G` is not the
zero sheaf. -/
@[stacks 05LH] #check
  (AlgebraicGeometry.Scheme.Etale.exists_nonzero_vanishingOnFields :
    ∃ G : Sheaf Scheme.etaleTopology AddCommGrpCat.{u},
      vanishesOnFields G ∧
        Scheme.PreservesDirectedAffineLimits (G.obj ⋙ forget AddCommGrpCat.{u}) ∧
        iso_map_of_isThickening G ∧
        ¬ IsZero G)
