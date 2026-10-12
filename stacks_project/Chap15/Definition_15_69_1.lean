/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ProjectiveAmplitude

@[expose] public section

/-!
# Definition 15.69.1: projective amplitude

@stack 0A5N
-/

/- Definition 15.69.1 (0A5N): finite projective dimension and projective amplitude in a fixed
interval are owned by the reusable derived-category projective-amplitude API. -/
@[stacks 0A5N "(1), finite projective dimension"]
#check @CategoryTheory.HasFiniteProjectiveDimension

@[stacks 0A5N "(2), projective amplitude"]
#check @CategoryTheory.HasProjectiveAmplitudeIn

/- The abstract owner works for every abelian category with a derived category. -/
@[stacks 0A5N "abstract projective amplitude"]
#check @CategoryTheory.DerivedCategory.HasProjectiveAmplitudeIn

@[stacks 0A5N "abstract finite projective dimension"]
#check @CategoryTheory.DerivedCategory.HasFiniteProjectiveDimension

/- The bundled representative carries its support bounds and termwise projectivity as reusable
instances, avoiding chapter-local instance reconstruction. -/
@[stacks 0A5N "bundled projective representative"]
#check @CochainComplex.ProjectiveIn

@[stacks 0A5N "constructor for a bundled projective representative"]
#check @CochainComplex.ProjectiveIn.of

@[stacks 0A5N "underlying complex of the bundled constructor"]
#check @CochainComplex.ProjectiveIn.of_obj

@[stacks 0A5N "K-projectivity of a bundled projective representative"]
#check @CochainComplex.ProjectiveIn.isKProjective

@[stacks 0A5N "bounded-above projective representative bridge"]
#check @CochainComplex.ProjectiveIn.toProjectiveMinus

@[stacks 0A5N "projective amplitude representative bridge"]
#check @CategoryTheory.hasProjectiveAmplitudeIn_iff_exists_representative

@[stacks 0A5N "bundled projective amplitude bridge"]
#check @CategoryTheory.hasProjectiveAmplitudeIn_iff_exists_bundled

@[stacks 0A5N "finite projective dimension interval bridge"]
#check @CategoryTheory.hasFiniteProjectiveDimension_iff
