module

public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap66.Lemma_66_18_6_Site
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap71.Lemma_71_7_5_RegularSection

/-!
# Lemma 71.7.5

A global function on an algebraic space is a regular section of `𝒪_X` if and only if it
is a nonzerodivisor in every étale local ring, if and only if its restriction to every
affine étale scheme is a nonzerodivisor, and if and only if it becomes a regular section
after pullback along some surjective étale morphism from a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Lemma 71.7.5 (1): a global function `f` of an algebraic space `X` is a regular section
of `𝒪_X` if and only if, for every geometric point `x̄` and every lift of `x̄` through an
étale neighbourhood, the image of `f` in the étale local ring `𝒪_{X, x̄}` is a
nonzerodivisor. -/
@[stacks 0844]
theorem isRegularStructureSection_iff_stalkwise (f : globalSectionsRing X) :
    IsRegularStructureSection f ↔
      ∀ (xbar : GeometricPoint X) (U : smallEtaleSite X)
        (l : xbar.toSmallEtalePoint.fiber.obj U),
        IsSMulRegular (structureSheafStalk xbar) (structureSectionGerm xbar U l f) :=
  sorry

/-- Lemma 71.7.5 (2): a global function `f` of an algebraic space `X` is a regular section
of `𝒪_X` if and only if, for every affine scheme étale over `X`, the restriction of `f` is
a nonzerodivisor of the coordinate ring. -/
@[stacks 0844]
theorem isRegularStructureSection_iff_forall_affineEtale (f : globalSectionsRing X) :
    IsRegularStructureSection f ↔
      ∀ U : affineEtaleSite X,
        IsSMulRegular Γ((smallEtaleToScheme X).obj U.obj, ⊤)
          (restrictGlobalSection U.obj f) :=
  sorry

/-- Lemma 71.7.5 (3): a global function `f` of an algebraic space `X` is a regular section
of `𝒪_X` if and only if there exists a scheme `U` and a surjective étale morphism `U ⟶ X`
such that the restriction of `f` is a regular section of `𝒪_U`. -/
@[stacks 0844]
theorem isRegularStructureSection_iff_exists_surjectiveEtale (f : globalSectionsRing X) :
    IsRegularStructureSection f ↔
      ∃ U : smallEtaleSite X,
        Surjective U.hom ∧
          IsRegularSchemeStructureSection (restrictGlobalSection U f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
