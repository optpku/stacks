/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeTheoreticSupport

/-!
# Existence of scheme-theoretic supports of finite-type quasi-coherent modules

A finite-type quasi-coherent module on an algebraic space is the pushforward of
a quasi-coherent module from a smallest closed subspace. Étale inverse image
recovers the scheme-theoretic support on a scheme.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 67.15.3 (1): Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `F` be a finite type quasi-coherent `𝒪_X`-module. There exists a smallest
closed subspace `i : Z ⟶ X` such that there exists a quasi-coherent `𝒪_Z`-module
`G` with `(pushforward i).obj G ≅ F`. -/
@[stacks 07U0] #check (AlgebraicGeometry.AlgebraicSpace.Modules.exists_schemeTheoreticSupport :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType],
    ∃ (Z : AlgebraicSpace S) (i : Z ⟶ X), IsSchemeTheoreticSupport F i)

/- There exists a least closed subspace of `X` through which `F` is a
quasi-coherent pushforward. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.exists_least_closedSubspace :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType],
    ∃ Z : ClosedSubspace X,
      (∃ G : Z.X.Modules,
        G.IsQuasicoherent ∧ Nonempty ((pushforward Z.ι).obj G ≅ F)) ∧
        ∀ Z' : ClosedSubspace X,
          (∃ G' : Z'.X.Modules,
            G'.IsQuasicoherent ∧ Nonempty ((pushforward Z'.ι).obj G' ≅ F)) →
            ∃ k : Z.X ⟶ Z'.X, k ≫ Z'.ι = Z.ι)

/- Lemma 67.15.3 (2): If `U` is a scheme and `φ : ofOver U ⟶ X` is an étale
morphism, then `Z ×_X U` is a scheme-theoretic support of `φ* F`. -/
@[stacks 07U0] #check (AlgebraicGeometry.AlgebraicSpace.Modules.isSchemeTheoreticSupport_inverseImage_etale :
  ∀ {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsSchemeTheoreticSupport F i]
    {U : Over S} (φ : ofOver U ⟶ X) [Etale φ],
    IsSchemeTheoreticSupport ((pullback φ).obj F) (inverseImageι φ i))

/- Under an étale morphism from a scheme, the inverse image of a
scheme-theoretic support of `F` is uniquely isomorphic over `ofOver U` to the
algebraic space of the scheme-theoretic support of the restriction of `φ* F`. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.inverseImage_etale_iso_schemeTheoreticSupport :
  ∀ {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsSchemeTheoreticSupport F i]
    {U : Over S} (φ : ofOver U ⟶ X) [Etale φ],
    ∃! e : inverseImage φ i ≅
        ofOverClosedSubscheme U (etalePullbackSchemeTheoreticSupport F φ),
      e.hom ≫ ofOverClosedSubschemeι U (etalePullbackSchemeTheoreticSupport F φ) =
        inverseImageι φ i)

/- Lemma 67.15.3 (3): The quasi-coherent sheaf `G` is unique up to unique
isomorphism. -/
@[stacks 07U0] #check (AlgebraicGeometry.AlgebraicSpace.Modules.existsUnique_iso_of_pushforward_iso :
  ∀ {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} {F : X.Modules} (i : Z ⟶ X) [IsClosedImmersion i]
    (G G' : Z.Modules) [G.IsQuasicoherent] [G'.IsQuasicoherent]
    (e : (pushforward i).obj G ≅ F) (e' : (pushforward i).obj G' ≅ F),
    ∃! α : G ≅ G', ((pushforward i).mapIso α).trans e' = e)

/- Lemma 67.15.3 (4): The quasi-coherent sheaf `G` is of finite type. -/
@[stacks 07U0] #check (AlgebraicGeometry.AlgebraicSpace.Modules.isFiniteType_of_pushforward_iso :
  ∀ {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (i : Z ⟶ X) [IsSchemeTheoreticSupport F i] (G : Z.Modules) [G.IsQuasicoherent]
    (e : (pushforward i).obj G ≅ F),
    G.IsFiniteType)

/- Lemma 67.15.3 (5): The support of `F` is `|Z|`. -/
@[stacks 07U0] #check (AlgebraicGeometry.AlgebraicSpace.Modules.moduleSupport_eq_pointsSet :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (i : Z ⟶ X)
    [IsClosedImmersion i] [IsSchemeTheoreticSupport F i],
    moduleSupport F = ClosedSubspace.pointsSet (ClosedSubspace.ofι i))

/- The support of a quasi-coherent descent `G` of `F` along a scheme-theoretic
support is all of `|Z|`. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.moduleSupport_eq_univ_of_pushforward_iso :
  ∀ {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (i : Z ⟶ X) [IsSchemeTheoreticSupport F i] (G : Z.Modules) [G.IsQuasicoherent]
    (e : (pushforward i).obj G ≅ F),
    moduleSupport G = (Set.univ : Set (Points Z)))
