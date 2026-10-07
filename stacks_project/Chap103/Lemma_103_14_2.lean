module

public import stacks_project.Chap103.Lemma_103_14_2_Ringed
public import stacks_project.Chap103.Lemma_103_14_2_Sites
public import stacks_project.Chap103.Lemma_103_14_2_Topos
import StacksCheckRecall

/-!
The lisse-étale and flat-fppf inclusions of an algebraic stack are fully
faithful, continuous and cocontinuous, and therefore induce morphisms of
(ringed) topoi whose inverse images are restriction.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.GroupoidsOver CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]

/- Lemma 103.14.2 (1): the inclusion functor X_lisse,étale ⟶ X_étale is fully
faithful. -/
@[stacks 0788]
#check (inferInstance : (lisseEtaleInclusion X).Full)

/- Lemma 103.14.2 (2): the lisse-étale inclusion is faithful. -/
@[stacks 0788]
#check (inferInstance : (lisseEtaleInclusion X).Faithful)

/- Lemma 103.14.2 (3): the lisse-étale inclusion is continuous. -/
@[stacks 0788]
#check (lisseEtaleInclusion.instIsContinuous X)

/- Lemma 103.14.2 (4): the lisse-étale inclusion is cocontinuous. -/
@[stacks 0788]
#check (lisseEtaleInclusion.instIsCocontinuous X)

/- Lemma 103.14.2 (5): the inclusion induces a morphism of topoi
g : Sh(X_lisse,étale) ⟶ Sh(X_étale). -/
@[stacks 0788]
#check (lisseEtaleToposHom X)

/- Lemma 103.14.2 (6): g⁻¹ is given by restriction. -/
@[stacks 0788]
#check (lisseEtaleRestrictionComparison X)

/- Lemma 103.14.2 (7): the restriction comparison is an isomorphism. -/
@[stacks 0788]
#check (lisseEtaleRestrictionComparison.instIsIso X)

/- Lemma 103.14.2 (8): g⁻¹ has a left adjoint g_!^{Sh} on sheaves of sets. -/
@[stacks 0788]
#check (lisseEtaleLowerShriek X)

/- Lemma 103.14.2 (9): set-valued lower shriek is left adjoint to
restriction. -/
@[stacks 0788]
#check (lisseEtaleLowerShriek.adjunction X)

/- Lemma 103.14.2 (10): the adjunction map g⁻¹ g_* ⟶ id is an isomorphism. -/
@[stacks 0788]
#check (lisseEtaleSheafAdjunctionCocontinuous_counit_app_isIso X)

/- Lemma 103.14.2 (11): the adjunction map id ⟶ g⁻¹ g_!^{Sh} is an
isomorphism. -/
@[stacks 0788]
#check (lisseEtaleLowerShriek_unit_app_isIso X)

/- Lemma 103.14.2 (12): g⁻¹ has a left adjoint g_! on abelian sheaves. -/
@[stacks 0788]
#check (lisseEtaleAbelianLowerShriek X)

/- Lemma 103.14.2 (13): the adjunction map id ⟶ g⁻¹ g_! is an isomorphism on
abelian sheaves. -/
@[stacks 0788]
#check (lisseEtaleAbelianLowerShriek_unit_app_isIso X)

/- Lemma 103.14.2 (14): g⁻¹ 𝒪_X = 𝒪_{X_lisse,étale}. -/
@[stacks 0788]
#check (lisseEtaleStructureSheaf X)

/- Lemma 103.14.2 (15): g induces a morphism of ringed topoi. -/
@[stacks 0788]
#check (lisseEtaleRingedToposHom X)

/- Lemma 103.14.2 (16): the structure map is an isomorphism, so g⁻¹ = g^*. -/
@[stacks 0788]
#check (lisseEtaleRingedToposHom.structureMap_isIso X)

/- Lemma 103.14.2 (17): module pullback along g preserves finite limits. -/
@[stacks 0788]
#check (lisseEtaleRingedToposHom.modulePullback_preservesFiniteLimits X)

/- Lemma 103.14.2 (18): the inclusion functor X_flat,fppf ⟶ X_fppf is fully
faithful. -/
@[stacks 0788]
#check (inferInstance : (flatFppfInclusion X).Full)

/- Lemma 103.14.2 (19): the flat-fppf inclusion is faithful. -/
@[stacks 0788]
#check (inferInstance : (flatFppfInclusion X).Faithful)

/- Lemma 103.14.2 (20): the flat-fppf inclusion is continuous. -/
@[stacks 0788]
#check (flatFppfInclusion.instIsContinuous X)

/- Lemma 103.14.2 (21): the flat-fppf inclusion is cocontinuous. -/
@[stacks 0788]
#check (flatFppfInclusion.instIsCocontinuous X)

/- Lemma 103.14.2 (22): the inclusion induces a morphism of topoi
g : Sh(X_flat,fppf) ⟶ Sh(X_fppf). -/
@[stacks 0788]
#check (flatFppfToposHom X)

/- Lemma 103.14.2 (23): g⁻¹ is given by restriction. -/
@[stacks 0788]
#check (flatFppfRestrictionComparison X)

/- Lemma 103.14.2 (24): the restriction comparison is an isomorphism. -/
@[stacks 0788]
#check (flatFppfRestrictionComparison.instIsIso X)

/- Lemma 103.14.2 (25): g⁻¹ has a left adjoint g_!^{Sh} on sheaves of sets. -/
@[stacks 0788]
#check (flatFppfLowerShriek X)

/- Lemma 103.14.2 (26): set-valued lower shriek is left adjoint to
restriction. -/
@[stacks 0788]
#check (flatFppfLowerShriek.adjunction X)

/- Lemma 103.14.2 (27): the adjunction map g⁻¹ g_* ⟶ id is an isomorphism. -/
@[stacks 0788]
#check (flatFppfSheafAdjunctionCocontinuous_counit_app_isIso X)

/- Lemma 103.14.2 (28): the adjunction map id ⟶ g⁻¹ g_!^{Sh} is an
isomorphism. -/
@[stacks 0788]
#check (flatFppfLowerShriek_unit_app_isIso X)

/- Lemma 103.14.2 (29): g⁻¹ has a left adjoint g_! on abelian sheaves. -/
@[stacks 0788]
#check (flatFppfAbelianLowerShriek X)

/- Lemma 103.14.2 (30): the adjunction map id ⟶ g⁻¹ g_! is an isomorphism on
abelian sheaves. -/
@[stacks 0788]
#check (flatFppfAbelianLowerShriek_unit_app_isIso X)

/- Lemma 103.14.2 (31): g⁻¹ 𝒪_X = 𝒪_{X_flat,fppf}. -/
@[stacks 0788]
#check (flatFppfStructureSheaf X)

/- Lemma 103.14.2 (32): g induces a morphism of ringed topoi. -/
@[stacks 0788]
#check (flatFppfRingedToposHom X)

/- Lemma 103.14.2 (33): the structure map is an isomorphism, so g⁻¹ = g^*. -/
@[stacks 0788]
#check (flatFppfRingedToposHom.structureMap_isIso X)

/- Lemma 103.14.2 (34): module pullback along g preserves finite limits. -/
@[stacks 0788]
#check (flatFppfRingedToposHom.modulePullback_preservesFiniteLimits X)

end AlgebraicGeometry.AlgebraicStack
