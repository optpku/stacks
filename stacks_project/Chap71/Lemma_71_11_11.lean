/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.DegreeOne

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.RelativeProj
open SheafOfModules.RingedSite
universe u

/- Lemma 71.11.11: relative Proj represents the functor of invertible-module triples. -/
@[stacks 085D] #check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.exists_natIso_of_generatedByDegreeOne :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    (hgenerated : GeneratedByDegreeOne 𝒜)
    (deg : DegreePieces 𝒜)
    (F₁ : DegreeOneFunctor X 𝒜) (hF₁ : F₁.IsAssociatedToTriples deg)
    (P : Twist 𝒜 deg),
    ∃ e : P.space.functorOfPoints ≅ F₁.toFunctor,
      e.hom ≫ F₁.baseMap = P.π)

/- The canonical degree-one map is surjective. -/
#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.canonicalMap_epi_of_generatedByDegreeOne :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    (hgenerated : GeneratedByDegreeOne 𝒜)
    (deg : DegreePieces 𝒜) (P : Twist 𝒜 deg),
    Epi (Twist.canonicalMap P))

/- The integral twists are invertible. -/
#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.twist_invertible_of_generatedByDegreeOne :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    (hgenerated : GeneratedByDegreeOne 𝒜)
    (deg : DegreePieces 𝒜) (P : Twist 𝒜 deg),
    ∀ n : ℤ, isInvertibleObject (P.twistModule n))

/- The integral multiplication maps are isomorphisms. -/
#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.mulHom_isIso_of_generatedByDegreeOne :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    (hgenerated : GeneratedByDegreeOne 𝒜)
    (deg : DegreePieces 𝒜) (P : Twist 𝒜 deg),
    ∀ n m : ℤ, IsIso (GradedAlgebraSheaf.mulHom P.twistAlgebra n m))

