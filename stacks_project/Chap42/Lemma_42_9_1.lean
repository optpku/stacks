/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.GenericPointLength
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DeltaDimension.GenericPoints

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/- Lemma 42.9.1 (1): At a generic point of an irreducible component of a closed
subscheme locally of finite type over a universally catenary scheme, the subscheme stalk
has finite length as a module over the ambient stalk. -/
@[stacks 02QT] #check
  (AlgebraicGeometry.Scheme.Hom.closedSubschemeStalk_length_lt_top_at_genericPoint :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
      (δ : S → ℤ) [IsDimensionFunction δ] (Z : X.IdealSheafData)
      (ξ : genericPoints Z.subscheme),
    let 𝒪Z := Z.subscheme.presheaf
    Module.length (X.presheaf.stalk (Z.subschemeι ξ.1))
      ((ModuleCat.restrictScalars (Z.subschemeι.stalkMap ξ.1).hom).obj
        (ModuleCat.of (𝒪Z.stalk ξ.1) (𝒪Z.stalk ξ.1))) < ⊤)

/- Lemma 42.9.1 (2): A point of a closed subscheme that attains an upper bound for
its `δ`-dimension is a generic point of an irreducible component. -/
@[stacks 02QT] #check
  (AlgebraicGeometry.Scheme.Hom.mem_genericPoints_of_closedSubschemeDeltaDimension_le :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
      (δ : S → ℤ) [IsDimensionFunction δ] (Z : X.IdealSheafData)
      (ξ : Z.subscheme) (k : ℤ),
      f.closedSubschemeDeltaDimension δ Z ≤ (k : EInt) →
        f.relativeDimensionFunction δ (Z.subschemeι ξ) = k →
          ξ ∈ genericPoints Z.subscheme)
