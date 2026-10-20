module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.NonfiniteGlobalSections

/-!
# Non-finite global sections of a projective scheme
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma [Stacks 0HAT] (1): a projective scheme over a ring can have non-finite
structure-sheaf global sections. -/
@[stacks 0HAT] #check
  (AlgebraicGeometry.Projective.exists_globalSections_not_finite :
    ∃ (R : Type u) (_ : CommRing R) (X : Scheme.{u}) (f : X ⟶ Spec (.of R)),
      Projective f ∧ ¬ Module.Finite R (Scheme.Hom.globalSectionsAlg f))

/- Lemma [Stacks 0HAT] (2): a finite type quasi-coherent module on projective
one-space can have non-finite global sections. -/
@[stacks 0HAT] #check
  (AlgebraicGeometry.ProjectiveSpace.exists_finiteTypeQuasicoherent_globalSections_not_finite :
    ∃ (R : Type u) (_ : CommRing R) (F : (ProjectiveSpace.scheme R 1).Modules),
      F.IsFiniteType ∧ F.IsQuasicoherent ∧
        ¬ Module.Finite R
            (Scheme.Hom.globalSectionsMod (ProjectiveSpace.toSpec R 1) F))
