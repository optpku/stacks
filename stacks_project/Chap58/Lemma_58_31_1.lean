/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.CodimensionOneRamification
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

/- Lemma 58.31.1 (1): unramified finite-étale covers remain unramified in codimension one
after pullback along a morphism preserving the boundary generic points. -/
@[stacks 0EYD] #check
  (AlgebraicGeometry.Scheme.FiniteEtale.IsUnramifiedInCodimensionOne.baseChange :
    ∀ {X X' : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian X']
      (f : X' ⟶ X) (U : X.Opens)
      (hU : Dense (U : Set X)) (hU' : Dense (f ⁻¹ᵁ U : Set X'))
      [HasDVRBoundary X U] [HasDVRBoundary X' (f ⁻¹ᵁ U)],
      (∀ Z' : PrimeDivisor X',
        Disjoint (Z'.support : Set X') (f ⁻¹ᵁ U : Set X') →
          ∃ Z : PrimeDivisor X,
            Disjoint (Z.support : Set X) (U : Set X) ∧
              f Z'.genericPoint = Z.genericPoint) →
        ∀ (Y : Scheme.FiniteEtale U.toScheme),
          IsUnramifiedInCodimensionOne U hU Y →
            IsUnramifiedInCodimensionOne (f ⁻¹ᵁ U) hU'
              ((Scheme.finiteEtaleBaseChange (f.resLE U (f ⁻¹ᵁ U) le_rfl)).obj Y))

/- Lemma 58.31.1 (2): tamely ramified finite-étale covers remain tamely ramified in codimension
one after pullback along a morphism preserving the boundary generic points. -/
@[stacks 0EYD] #check
  (AlgebraicGeometry.Scheme.FiniteEtale.IsTamelyRamifiedInCodimensionOne.baseChange :
    ∀ {X X' : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian X']
      (f : X' ⟶ X) (U : X.Opens)
      (hU : Dense (U : Set X)) (hU' : Dense (f ⁻¹ᵁ U : Set X'))
      [HasDVRBoundary X U] [HasDVRBoundary X' (f ⁻¹ᵁ U)],
      (∀ Z' : PrimeDivisor X',
        Disjoint (Z'.support : Set X') (f ⁻¹ᵁ U : Set X') →
          ∃ Z : PrimeDivisor X,
            Disjoint (Z.support : Set X) (U : Set X) ∧
              f Z'.genericPoint = Z.genericPoint) →
        ∀ (Y : Scheme.FiniteEtale U.toScheme),
          IsTamelyRamifiedInCodimensionOne U hU Y →
            IsTamelyRamifiedInCodimensionOne (f ⁻¹ᵁ U) hU'
              ((Scheme.finiteEtaleBaseChange (f.resLE U (f ⁻¹ᵁ U) le_rfl)).obj Y))

end AlgebraicGeometry.Scheme.FiniteEtale
