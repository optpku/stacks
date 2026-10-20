/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Twist
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Commutative

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.RelativeProj
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

/-- Relative Proj of a commutative quasi-coherent graded algebra generated in degree one represents the functor of invertible-module triples with a degree-one-surjective graded map. -/
theorem exists_natIso_of_generatedByDegreeOne
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    (hgenerated : GeneratedByDegreeOne 𝒜)
    (deg : DegreePieces 𝒜)
    (F₁ : DegreeOneFunctor X 𝒜) (hF₁ : F₁.IsAssociatedToTriples deg)
    (P : Twist 𝒜 deg) :
    ∃ e : P.space.functorOfPoints ≅ F₁.toFunctor,
      e.hom ≫ F₁.baseMap = P.π :=
  sorry

/-- The canonical degree-one map on relative Proj is an epimorphism when the algebra is generated in degree one. -/
theorem canonicalMap_epi_of_generatedByDegreeOne
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    (hgenerated : GeneratedByDegreeOne 𝒜)
    (deg : DegreePieces 𝒜) (P : Twist 𝒜 deg) :
    Epi (Twist.canonicalMap P) :=
  sorry

/-- Every integral twist on relative Proj is invertible when the algebra is generated in degree one. -/
theorem twist_invertible_of_generatedByDegreeOne
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    (hgenerated : GeneratedByDegreeOne 𝒜)
    (deg : DegreePieces 𝒜) (P : Twist 𝒜 deg) :
    ∀ n : ℤ, isInvertibleObject (P.twistModule n) :=
  sorry

/-- Every integral twist multiplication on relative Proj is an isomorphism when the algebra is generated in degree one. -/
theorem mulHom_isIso_of_generatedByDegreeOne
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    (hgenerated : GeneratedByDegreeOne 𝒜)
    (deg : DegreePieces 𝒜) (P : Twist 𝒜 deg) :
    ∀ n m : ℤ, IsIso (GradedAlgebraSheaf.mulHom P.twistAlgebra n m) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
