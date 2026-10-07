module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom

@[expose] public section

/-!
# Bounded-above projective models for derived Hom

Lemma 15.74.2 (0A66): a bounded-above complex of projective modules computes derived Hom by its
ordinary Hom complex. In the repository's commutative `ModuleCat` specialization, the reusable
owner is `CochainComplex.ProjectiveMinus.representsRHom`.

@stack 0A66
-/

/- Lemma 15.74.2 (0A66): the ordinary Hom complex of a projective-minus source represents
canonical `RHom`. -/
@[stacks 0A66 "projective-minus Hom complex represents derived Hom"]
#check @CochainComplex.ProjectiveMinus.representsRHom

#check @CochainComplex.ProjectiveMinus.representsRHom_of_finiteProjective
#check @CochainComplex.ProjectiveMinus.representsRHom_of_models

#print axioms CochainComplex.ProjectiveMinus.representsRHom
