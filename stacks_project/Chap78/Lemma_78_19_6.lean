module

public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import stacks_project.Chap73.Definition_73_7_1_FppfCover
public import stacks_project.Chap73.Lemma_73_7_5
public import stacks_project.Chap78.Lemma_78_19_6_QuotientMap

/-!
# Lemma 78.19.6

Restriction of a pre-equivalence relation along a morphism of algebraic spaces
over the base induces an injective map of fppf quotient sheaves, which is an
isomorphism when the morphism is surjective as a map of sheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Limits
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.PreRelation

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- Lemma 78.19.6 (1): the restriction-induced map of fppf quotient sheaves
`U'/R' ⟶ U/R` is injective as a map of sheaves. -/
@[stacks 046P]
theorem quotientSheafMap_isLocallyInjective {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U U' : Over B} (P : PreRelation U) (g : U' ⟶ U) (hP : P.IsPreEquivalence) :
    Sheaf.IsLocallyInjective (P.quotientSheafMap g) :=
  sorry

/-- Lemma 78.19.6 (2): if `U' ⟶ U` is surjective as a map of fppf sheaves, then
the restriction-induced map `U'/R' ⟶ U/R` is an isomorphism of sheaves. -/
@[stacks 046P]
theorem quotientSheafMap_isIso_of_locallySurjective {S : Scheme.{u}}
    {B : AlgebraicSpace S} {U U' : Over B} (P : PreRelation U) (g : U' ⟶ U)
    (hP : P.IsPreEquivalence)
    (hg : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) g.left) :
    IsIso (P.quotientSheafMap g) :=
  sorry

/-- Lemma 78.19.6 (3): if `{g : U' ⟶ U}` is an fppf covering, then the
restriction-induced map `U'/R' ⟶ U/R` is an isomorphism of sheaves. -/
@[stacks 046P]
theorem quotientSheafMap_isIso_of_fppfCovering {S : Scheme.{u}}
    {B : AlgebraicSpace S} {U U' : Over B} (P : PreRelation U) (g : U' ⟶ U)
    (hP : P.IsPreEquivalence)
    [FppfCovering (fun _ : PUnit ↦ U'.left) (fun _ ↦ g.left)] :
    IsIso (P.quotientSheafMap g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
