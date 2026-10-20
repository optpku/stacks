/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction.Jacobson

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 42.7.5 (1): At the generic point of an integral closed subscheme, the relative
dimension is the integer cast of a natural number. -/
@[stacks 02QO] #check
  (AlgebraicGeometry.Scheme.Hom.relativeDimensionFunction_generic_eq_natCast :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (δ : S → ℤ)
      [UniversallyCatenary S] [JacobsonSpace S] [IsDimensionFunction δ]
      [LocallyOfFiniteType f] (hδ_closed : ∀ s ∈ closedPoints S, δ s = 0)
      (Z : X.IdealSheafData) [AlgebraicGeometry.IsIntegral Z.subscheme]
      (ξ : genericPoints Z.subscheme),
      f.relativeDimensionFunction δ (Z.subschemeι ξ.1) =
        (Int.toNat (f.relativeDimensionFunction δ (Z.subschemeι ξ.1)) : ℤ))

/- Lemma 42.7.5 (2): The Krull dimension of an integral closed subscheme equals the
relative dimension at its generic point. -/
@[stacks 02QO] #check
  (AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_eq_relativeDimensionFunction_generic :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (δ : S → ℤ)
      [UniversallyCatenary S] [JacobsonSpace S] [IsDimensionFunction δ]
      [LocallyOfFiniteType f] (hδ_closed : ∀ s ∈ closedPoints S, δ s = 0)
      (Z : X.IdealSheafData) [AlgebraicGeometry.IsIntegral Z.subscheme]
      (ξ : genericPoints Z.subscheme),
      topologicalKrullDim Z.subscheme =
        (Int.toNat (f.relativeDimensionFunction δ (Z.subschemeι ξ.1)) : WithBot ℕ∞))

/- Lemma 42.7.5 (3): At every closed point of an integral closed subscheme, the local
ring has Krull dimension equal to the relative dimension at the generic point. -/
@[stacks 02QO] #check
  (AlgebraicGeometry.Scheme.Hom.ringKrullDim_stalk_eq_relativeDimensionFunction_generic :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (δ : S → ℤ)
      [UniversallyCatenary S] [JacobsonSpace S] [IsDimensionFunction δ]
      [LocallyOfFiniteType f] (hδ_closed : ∀ s ∈ closedPoints S, δ s = 0)
      (Z : X.IdealSheafData) [AlgebraicGeometry.IsIntegral Z.subscheme]
      (ξ : genericPoints Z.subscheme) (z : Z.subscheme)
      (hz : z ∈ closedPoints Z.subscheme),
      ringKrullDim ((Z.subscheme).presheaf.stalk z) =
        (Int.toNat (f.relativeDimensionFunction δ (Z.subschemeι ξ.1)) : WithBot ℕ∞))

end AlgebraicGeometry.Scheme.Hom
