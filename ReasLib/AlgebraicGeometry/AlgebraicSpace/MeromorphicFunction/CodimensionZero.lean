/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.Algebra.Category.CommRingCat.ULift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MeromorphicFunction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.CodimensionZeroStalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRingHom

/-! # Meromorphic functions and codimension-zero stalk pushforwards -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The direct image of the structure sheaf of the marked stalk spectrum of a chart. -/
def codimZeroStalkPushforwardSheafUnlifted {S : Scheme.{u}} {X : AlgebraicSpace S}
    (c : codimZeroPoints X → OpenImmersionChart X) (η : codimZeroPoints X) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} :=
  (commRingPushforward (c η).stalkMap).obj (commStructureSheaf (ofOver (c η).stalkOver))

/-- The universe lift of the underlying presheaf of a marked stalk-ring direct image. -/
def codimZeroStalkPushforwardPresheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (c : codimZeroPoints X → OpenImmersionChart X) (η : codimZeroPoints X) :
    (smallEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  (codimZeroStalkPushforwardSheafUnlifted c η).obj ⋙ CommRingCat.universeLift.{u, u + 1}

/-- The lifted stalk-ring presheaf is composition of the direct image with universe lift. -/
theorem codimZeroStalkPushforwardPresheaf_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (c : codimZeroPoints X → OpenImmersionChart X) (η : codimZeroPoints X) :
    codimZeroStalkPushforwardPresheaf c η =
      (codimZeroStalkPushforwardSheafUnlifted c η).obj ⋙
        CommRingCat.universeLift.{u, u + 1} :=
  rfl

/-- Universe lifting the direct image of a marked stalk-ring sheaf preserves sheafness. -/
theorem codimZeroStalkPushforwardPresheaf_isSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (c : codimZeroPoints X → OpenImmersionChart X) (η : codimZeroPoints X) :
    Presheaf.IsSheaf (smallEtaleTopology X) (codimZeroStalkPushforwardPresheaf c η) :=
  sorry

/-- The universe-lifted direct image of a marked stalk-ring sheaf. -/
def codimZeroStalkPushforwardSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (c : codimZeroPoints X → OpenImmersionChart X) (η : codimZeroPoints X) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u + 1} :=
  ⟨codimZeroStalkPushforwardPresheaf c η, codimZeroStalkPushforwardPresheaf_isSheaf c η⟩

/-- The lifted stalk-ring sheaf has the universe-lifted direct-image presheaf. -/
theorem codimZeroStalkPushforwardSheaf_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (c : codimZeroPoints X → OpenImmersionChart X) (η : codimZeroPoints X) :
    (codimZeroStalkPushforwardSheaf c η).obj = codimZeroStalkPushforwardPresheaf c η :=
  rfl

/-- The categorical product of the lifted stalk-ring direct images at codimension-zero points. -/
def codimZeroStalkPushforwardProductSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (c : codimZeroPoints X → OpenImmersionChart X) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u + 1} :=
  ∏ᶜ fun η : codimZeroPoints X ↦ codimZeroStalkPushforwardSheaf c η

/-- Meromorphic functions form the product of the codimension-zero stalk-ring direct images
when weakly associated points have codimension zero, irreducible components are finite on
compact étale opens, and codimension-zero points have monomorphic field representatives. -/
theorem meromorphicFunctionSheaf_iso_codimZeroStalkPushforwardProduct
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (c : codimZeroPoints X → OpenImmersionChart X)
    (hc : ∀ η, Points.mapOfOver (c η).ι (c η).u = η) :
    IsIsomorphic (meromorphicFunctionSheaf X) (codimZeroStalkPushforwardProductSheaf c) :=
  sorry

/-- Rational functions agree with global meromorphic functions when weakly associated points
have codimension zero, irreducible components are finite on compact étale opens, and
codimension-zero points have monomorphic field representatives. -/
theorem rationalFunctionRing_iso_meromorphicFunctions {S : Scheme.{u}}
    (X : AlgebraicSpace S) [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η) :
    IsIsomorphic (rationalFunctionRing X) (meromorphicFunctions X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
