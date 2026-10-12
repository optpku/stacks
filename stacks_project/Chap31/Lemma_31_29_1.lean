/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RankOneReflexive.Tensor
import StacksCheckRecall

/-!
# Lemma 31.29.1

Reflexive tensor products of rank-one coherent reflexive modules.

@stack 0EBL
-/

@[expose] public section

universe u

/- Lemma 31.29.1 (1): For coherent reflexive modules on an integral locally Noetherian normal
scheme, the canonical map from the reflexive hull of dual tensor to internal Hom is an
isomorphism. -/
@[stacks 0EBL] #check
  (AlgebraicGeometry.Scheme.Modules.isIso_reflexiveHullDualTensorToInternalHom :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
      [AlgebraicGeometry.IsLocallyNoetherian X],
      X.isNormal → ∀ (ℱ 𝒢 : X.Modules) [ℱ.IsCoherent] [𝒢.IsCoherent]
        [AlgebraicGeometry.Scheme.Modules.IsReflexive ℱ]
        [AlgebraicGeometry.Scheme.Modules.IsReflexive 𝒢],
        CategoryTheory.IsIso
          (AlgebraicGeometry.Scheme.Modules.reflexiveHullDualTensorToInternalHom ℱ 𝒢))

/- Lemma 31.29.1 (2): Reflexive-hull tensor product defines an additive commutative group on
isomorphism classes of rank-one coherent reflexive modules. -/
@[stacks 0EBL] #check
  (AlgebraicGeometry.Scheme.Modules.RankOneReflexiveIsoClass.addCommGroup :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
      [AlgebraicGeometry.IsLocallyNoetherian X],
      X.isNormal →
        AddCommGroup (AlgebraicGeometry.Scheme.Modules.RankOneReflexiveIsoClass X))

/- Addition is represented by reflexive-hull tensor product. -/
#check
  (AlgebraicGeometry.Scheme.Modules.RankOneReflexiveIsoClass.addCommGroup_add :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
      [AlgebraicGeometry.IsLocallyNoetherian X]
      (hXnormal : X.isNormal)
      (ℱ 𝒢 : AlgebraicGeometry.Scheme.Modules.RankOneReflexiveModule X),
      (AlgebraicGeometry.Scheme.Modules.RankOneReflexiveIsoClass.addCommGroup hXnormal).add
          (CategoryTheory.toSkeleton ℱ) (CategoryTheory.toSkeleton 𝒢) =
        CategoryTheory.toSkeleton
          (AlgebraicGeometry.Scheme.Modules.RankOneReflexiveModule.tensor ℱ 𝒢))
