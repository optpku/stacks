/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle.Relative
import StacksCheckRecall

open CategoryTheory

universe u

/- Definition 42.10.2: In the setting of `Situation 42.7.1`, the degree-`k`
cycle associated to a coherent module `F` has, at each minimal point of
`moduleSupport F` of relative dimension `k`, the finite length of the stalk of
`F` as coefficient, and coefficient zero elsewhere. The source assumption
`dimδ(moduleSupport F) ≤ k` restricts this application, while the canonical
constructor is valid without that bound. -/
@[stacks 02QX] #check
  (AlgebraicGeometry.Scheme.Modules.relativeAssociatedCycle :
    {X S : AlgebraicGeometry.Scheme.{u}} → (p : X ⟶ S) →
      [AlgebraicGeometry.UniversallyCatenary S] →
      [AlgebraicGeometry.LocallyOfFiniteType p] →
      (δ : S → ℤ) → [IsDimensionFunction δ] →
      (F : X.Modules) → [F.IsCoherent] → (k : ℤ) →
      AlgebraicGeometry.CycleGroup X (p.relativeDimensionFunction δ) k)

#check
  (AlgebraicGeometry.Scheme.Modules.relativeAssociatedCycle_toAlgebraicCycle :
    {X S : AlgebraicGeometry.Scheme.{u}} → (p : X ⟶ S) →
      [AlgebraicGeometry.UniversallyCatenary S] →
      [AlgebraicGeometry.LocallyOfFiniteType p] →
      (δ : S → ℤ) → [IsDimensionFunction δ] →
      (F : X.Modules) → [hF : F.IsCoherent] → (k : ℤ) → (x : X) →
      AlgebraicGeometry.CycleGroup.toAlgebraicCycle
          (p.relativeDimensionFunction δ) k
          (AlgebraicGeometry.Scheme.Modules.relativeAssociatedCycle p δ F k) x =
        @AlgebraicGeometry.Scheme.Modules.associatedCycle X
          (AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian p) F hF
          (p.relativeDimensionFunction δ) k x)

#check
  (AlgebraicGeometry.Scheme.Modules.associatedCycle_apply :
    {X : AlgebraicGeometry.Scheme.{u}} → [AlgebraicGeometry.IsLocallyNoetherian X] →
      (F : X.Modules) → [F.IsCoherent] → (d : X → ℤ) → (k : ℤ) → (x : X) →
      AlgebraicGeometry.Scheme.Modules.associatedCycle F d k x =
        @ite ℤ
          (x ∈ X.minimalSpecializationPoints
            (AlgebraicGeometry.Scheme.Modules.moduleSupport F) ∧ d x = k)
          (Classical.propDecidable _)
          ((Module.length (X.presheaf.stalk x)
            (AlgebraicGeometry.RingedSpace.stalkModuleCat F x)).toNat : ℤ)
          0)
