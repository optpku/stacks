/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Commutative
public import stacks_project.Chap71.Lemma_71_11_11_Functor
public import stacks_project.Chap71.Lemma_71_11_11_Triple
public import stacks_project.Chap71.Lemma_71_11_11_Twist

/-!
# Lemma 71.11.11

Relative Proj of a quasi-coherent graded algebra on an algebraic space, generated in
degree one, represents the functor of strict-equivalence classes of invertible-module triples,
the canonical map to `𝒪_P(1)` is surjective, and each twist is invertible with
multiplication isomorphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.RelativeProj
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

/-- Lemma 71.11.11 (1): if `𝒜` is generated as an `𝒜_0`-algebra by `𝒜_1`, then
`P = underline{Proj}_X(𝒜)` (an algebraic space étale-locally identified with scheme-level
`Proj` of a degree-one-generated section model, with `𝒪_P(n)` matching the actual twists)
represents the functor `F_1` of isomorphism classes of triples `(f, ℒ, ψ)` over schemes
`T` over `S`. -/
@[stacks 085D]
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

/-- Lemma 71.11.11 (2): the canonical map `π^* 𝒜_1 ⟶ 𝒪_P(1)` is surjective. -/
@[stacks 085D]
theorem canonicalMap_epi_of_generatedByDegreeOne
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    (hgenerated : GeneratedByDegreeOne 𝒜)
    (deg : DegreePieces 𝒜) (P : Twist 𝒜 deg) :
    Epi (Twist.canonicalMap P) :=
  sorry

/-- Lemma 71.11.11 (3): each `𝒪_P(n)` is invertible. -/
@[stacks 085D]
theorem twist_invertible_of_generatedByDegreeOne
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    (hgenerated : GeneratedByDegreeOne 𝒜)
    (deg : DegreePieces 𝒜) (P : Twist 𝒜 deg) :
    ∀ n : ℤ, isInvertibleObject (P.twistModule n) :=
  sorry

/-- Lemma 71.11.11 (4): multiplication induces isomorphisms
`𝒪_P(n) ⊗ 𝒪_P(m) ≅ 𝒪_P(n + m)`. -/
@[stacks 085D]
theorem mulHom_isIso_of_generatedByDegreeOne
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    (hgenerated : GeneratedByDegreeOne 𝒜)
    (deg : DegreePieces 𝒜) (P : Twist 𝒜 deg) :
    ∀ n m : ℤ, IsIso (GradedAlgebraSheaf.mulHom P.twistAlgebra n m) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
