/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import stacks_project.Chap66.Lemma_66_12_3
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_13_2_InverseImage
public import stacks_project.Chap67.Lemma_67_15_1_ModuleSupport
public import stacks_project.Chap67.Lemma_67_15_3_SchemeTheoreticSupport

/-!
# Existence of scheme-theoretic supports of finite-type quasi-coherent modules

A finite-type quasi-coherent module on an algebraic space is the pushforward of
a quasi-coherent module from a smallest closed subspace. Étale inverse image
recovers the scheme-theoretic support on a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 67.15.3 (1): Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `F` be a finite type quasi-coherent `𝒪_X`-module. There exists a smallest
closed subspace `i : Z ⟶ X` such that there exists a quasi-coherent `𝒪_Z`-module
`G` with `(pushforward i).obj G ≅ F`. -/
@[stacks 07U0]
theorem exists_schemeTheoreticSupport {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ (Z : AlgebraicSpace S) (i : Z ⟶ X), IsSchemeTheoreticSupport F i :=
  sorry

/-- There exists a least closed subspace of `X` through which `F` is a
quasi-coherent pushforward. -/
theorem exists_least_closedSubspace {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ Z : ClosedSubspace X,
      (∃ G : Z.X.Modules,
        G.IsQuasicoherent ∧ Nonempty ((pushforward Z.ι).obj G ≅ F)) ∧
        ∀ Z' : ClosedSubspace X,
          (∃ G' : Z'.X.Modules,
            G'.IsQuasicoherent ∧ Nonempty ((pushforward Z'.ι).obj G' ≅ F)) →
            ∃ k : Z.X ⟶ Z'.X, k ≫ Z'.ι = Z.ι :=
  sorry

/-- Lemma 67.15.3 (2): If `U` is a scheme and `φ : ofOver U ⟶ X` is an étale
morphism, then `Z ×_X U` is a scheme-theoretic support of `φ* F`. -/
@[stacks 07U0]
theorem isSchemeTheoreticSupport_inverseImage_etale {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsSchemeTheoreticSupport F i]
    {U : Over S} (φ : ofOver U ⟶ X) [Etale φ] :
    IsSchemeTheoreticSupport ((pullback φ).obj F) (inverseImageι φ i) :=
  sorry

/-- Under an étale morphism from a scheme, the inverse image of a
scheme-theoretic support of `F` is uniquely isomorphic over `ofOver U` to the
algebraic space of the scheme-theoretic support of the restriction of `φ* F`. -/
theorem inverseImage_etale_iso_schemeTheoreticSupport {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsSchemeTheoreticSupport F i]
    {U : Over S} (φ : ofOver U ⟶ X) [Etale φ] :
    ∃! e : inverseImage φ i ≅
        ofOverClosedSubscheme U (etalePullbackSchemeTheoreticSupport F φ),
      e.hom ≫ ofOverClosedSubschemeι U (etalePullbackSchemeTheoreticSupport F φ) =
        inverseImageι φ i :=
  sorry

/-- Lemma 67.15.3 (3): The quasi-coherent sheaf `G` is unique up to unique
isomorphism. -/
@[stacks 07U0]
theorem existsUnique_iso_of_isSchemeTheoreticSupport {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (i : Z ⟶ X) [IsSchemeTheoreticSupport F i] (G G' : Z.Modules)
    [G.IsQuasicoherent] [G'.IsQuasicoherent]
    (e : (pushforward i).obj G ≅ F) (e' : (pushforward i).obj G' ≅ F) :
    ∃! α : G ≅ G', ((pushforward i).mapIso α).trans e' = e :=
  sorry

/-- Lemma 67.15.3 (4): The quasi-coherent sheaf `G` is of finite type. -/
@[stacks 07U0]
theorem isFiniteType_of_pushforward_iso {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (i : Z ⟶ X) [IsSchemeTheoreticSupport F i] (G : Z.Modules) [G.IsQuasicoherent]
    (e : (pushforward i).obj G ≅ F) : G.IsFiniteType :=
  sorry

/-- Lemma 67.15.3 (5): The support of `F` is `|Z|`. -/
@[stacks 07U0]
theorem moduleSupport_eq_pointsSet {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (i : Z ⟶ X)
    [IsClosedImmersion i] [IsSchemeTheoreticSupport F i] :
    moduleSupport F = ClosedSubspace.pointsSet (ClosedSubspace.ofι i) :=
  sorry

/-- The support of a quasi-coherent descent `G` of `F` along a scheme-theoretic
support is all of `|Z|`. -/
theorem moduleSupport_eq_univ_of_pushforward_iso {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (i : Z ⟶ X) [IsSchemeTheoreticSupport F i] (G : Z.Modules) [G.IsQuasicoherent]
    (e : (pushforward i).obj G ≅ F) :
    moduleSupport G = (Set.univ : Set (Points Z)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
