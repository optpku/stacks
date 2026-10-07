module

public import stacks_project.Chap59.Lemma_59_65_1_Equivalence
public import stacks_project.Chap59.Lemma_59_65_1_StalkRepresentation
public import stacks_project.Chap59.Lemma_59_65_1_Forward
public import stacks_project.Chap59.Lemma_59_65_1_ModuleSheafInverse
public import stacks_project.Chap59.Lemma_59_65_1_StalkComparison
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.Scheme

universe u

/- Lemma 59.65.1 (1): finite locally constant sheaves of sets on the small étale site of a
connected scheme `X` are equivalent to finite `π₁(X, x̄)`-sets. -/
@[stacks 0DV5]
#check finiteLocallyConstant_equivalence_finitePi1Sets

/- Lemma 59.65.1 (2): finite locally constant sheaves of abelian groups on the small étale site
of a connected scheme `X` are equivalent to finite `π₁(X, x̄)`-modules. -/
@[stacks 0DV5]
#check finiteLocallyConstantAddCommGrp_equivalence_finitePi1Modules

/- Lemma 59.65.1 (3): for a finite ring `Λ`, finite-type locally constant sheaves of `Λ`-modules
on the small étale site of a connected scheme `X` are equivalent to finite `π₁(X, x̄)`-modules
with a commuting `Λ`-module structure. -/
@[stacks 0DV5]
#check finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules
