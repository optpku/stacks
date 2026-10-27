/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap42.Lemma_42_62_1_IntersectionProduct
public import stacks_project.Chap42.Lemma_42_62_5_IntersectionProduct
public import stacks_project.Chap42.Proposition_42_60_2
public import stacks_project.Chap42.«42_37_1_1_FundamentalCycle»
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

public import ReasLib.AlgebraicGeometry.BivariantClass.Fundamental

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.BivariantClass

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- The degree-`d` fundamental Chow class of a scheme locally of finite type over a field. -/
def relativeFundamentalClass {k : Type u} [Field k] (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] (d : ℕ) : RelativeChow (fun _ ↦ 0) X (d : ℤ) :=
  RelativeChow.fundamentalClass (fun _ ↦ 0) X (d : ℤ)

end AlgebraicGeometry.ChowGroup

/- Fundamental-class duality for smooth schemes of constant dimension over a field. -/
#check (AlgebraicGeometry.BivariantClass.capFundamentalEquiv :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Smooth X.hom] (d : ℕ)
    [RelativeDimension X.hom d] (p : ℤ),
    BivariantClass.group (fun _ ↦ 0) (𝟙 X) p ≃+
      RelativeChow (fun _ ↦ 0) X ((d : ℤ) - p))

/- Fundamental-class cap converts composition to the smooth diagonal intersection product. -/
#check (AlgebraicGeometry.BivariantClass.capFundamental_comp :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Smooth X.hom] (d : ℕ)
    [RelativeDimension X.hom d] (p q : ℤ)
    (c : group (fun _ ↦ 0) (𝟙 X) p) (c' : group (fun _ ↦ 0) (𝟙 X) q),
    capFundamental (fun _ ↦ 0) X (d : ℤ) (p + q)
        (identityComp (fun _ ↦ 0) X c c') =
      RelativeChow.castDegree (fun _ ↦ 0) (capFundamental_comp_degree d p q)
        (ChowGroup.smoothIntersectionProduct X d
          (capFundamental (fun _ ↦ 0) X (d : ℤ) p c)
          (capFundamental (fun _ ↦ 0) X (d : ℤ) q c')))
