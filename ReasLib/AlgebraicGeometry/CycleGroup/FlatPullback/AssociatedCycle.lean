/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.StructureSheafCycle
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFormula.Flat

/-!
# Associated cycles and flat pullback

This file records dimension bounds for inverse images under flat morphisms of
fixed relative dimension and compatibility of their cycles with flat pullback.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

/-- Flat pullback by a morphism of relative dimension `r` sends a closed
subscheme of `δ`-dimension at most `k` to one of dimension at most `k + r`. -/
theorem closedSubschemeDeltaDimension_comap_le
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [RelativeDimension f.left r]
    (Z : Y.left.IdealSheafData) (k : ℤ)
    (hZ : Y.hom.closedSubschemeDeltaDimension δ Z ≤ (k : EInt)) :
    X.hom.closedSubschemeDeltaDimension δ (Z.comap f.left) ≤
      ((k + (r : ℤ) : ℤ) : EInt) := sorry

end Scheme.Hom

namespace Scheme.Modules

/-- Flat pullback by a morphism of relative dimension `r` sends the support of
a coherent module of `δ`-dimension at most `k` to one of dimension at most
`k + r`. -/
theorem pullbackSupportDeltaDimension_le
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (F : Y.left.Modules) [F.IsCoherent] (k : ℤ)
    (hF : Y.hom.closedSubschemeDeltaDimension δ (schemeTheoreticSupport F) ≤ (k : EInt)) :
    X.hom.closedSubschemeDeltaDimension δ
        (schemeTheoreticSupport ((pullback f.left).obj F)) ≤
      ((k + (r : ℤ) : ℤ) : EInt) := sorry

/-- Flat pullback of the degree-`k` cycle associated to a coherent module is
the degree-`k + r` cycle associated to its pulled-back module. -/
theorem associatedCycle_pullback
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (F : Y.left.Modules) [hcoh : F.IsCoherent] (k : ℤ)
    (hF : Y.hom.closedSubschemeDeltaDimension δ (schemeTheoreticSupport F) ≤ (k : EInt)) :
    CycleGroup.flatPullback δ X Y f r k (relativeAssociatedCycle Y.hom δ F k) =
      relativeAssociatedCycle
        (hF := @pullback_isCoherent X.left Y.left
          (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (LocallyOfFiniteType.isLocallyNoetherian Y.hom) f.left F hcoh)
        X.hom δ ((pullback f.left).obj F) (k + (r : ℤ)) := sorry

end Scheme.Modules

namespace CycleGroup

/-- The degree-`k + r` cycle of an inverse-image closed subscheme is the flat
pullback of its degree-`k` cycle. -/
theorem flatPullback_closedSubschemeCycle
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (Z : Y.left.IdealSheafData) (k : ℤ)
    (hZ : Y.hom.closedSubschemeDeltaDimension δ Z ≤ (k : EInt)) :
    X.hom.closedSubschemeCycle δ (Z.comap f.left) (k + (r : ℤ))
        (Scheme.Hom.closedSubschemeDeltaDimension_comap_le δ X Y f r Z k hZ) =
      flatPullback δ X Y f r k (Y.hom.closedSubschemeCycle δ Z k hZ) := sorry

end CycleGroup

end AlgebraicGeometry
