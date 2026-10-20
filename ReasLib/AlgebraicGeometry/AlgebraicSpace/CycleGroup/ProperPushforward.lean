/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.IntegralImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidueField.Degree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Transfer
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyCatenary
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.Composition
public import ReasLib.Topology.Specialization.Dimension

/-!
# Proper pushforward of cycles on algebraic spaces

The proper pushforward of a cycle along a morphism of good algebraic spaces
weights fibres of `Points.map` by residue degree when relative dimension is
preserved, and otherwise by zero. This realises `f_*` on cycle groups of a
fixed relative dimension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function Set

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- Residue degree of a morphism of good algebraic spaces, using decency of the
source and target induced by the good structure morphisms. -/
noncomputable def residueDegreeAlong {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] (pY : Y ⟶ B) [QuasiSeparated pY]
    (h : X ⟶ Y) (x : Points X) : ℕ :=
  @residueDegree S X Y
    (@instIsDecent_of_isQuasiSeparated S X
      (IsQuasiSeparated.of_quasiSeparated pX))
    (@instIsDecent_of_isQuasiSeparated S Y
      (IsQuasiSeparated.of_quasiSeparated pY))
    h x

/-- Pushforward weight of a point: residue degree when `δ`-dimension is
preserved, and `0` otherwise. -/
noncomputable def mapCoeff {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX] (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) (f : X ⟶ Y) (x : Points X) : ℕ :=
  if (relativeDimensionFunction pX) δ x =
      (relativeDimensionFunction pY) δ (Points.map f x) then
    residueDegreeAlong pX pY f x
  else 0

/-- The pushforward weight is residue degree on dimension-preserving points and
zero otherwise. -/
theorem mapCoeff_eq {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX] (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) (f : X ⟶ Y) (x : Points X) :
    mapCoeff pX pY δ f x =
      if (relativeDimensionFunction pX) δ x =
          (relativeDimensionFunction pY) δ (Points.map f x) then
        residueDegreeAlong pX pY f x
      else 0 :=
  rfl

/-- Fibrewise residue-weighted sums along a proper morphism have locally finite
support. -/
theorem properPushforward_locallyFiniteSupport {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX)
    (α : Function.locallyFinsupp (Points X) ℤ) :
    LocallyFiniteSupport fun y : Points Y ↦
      ∑ᶠ x ∈ Points.map f ⁻¹' {y}, (mapCoeff pX pY δ f x : ℤ) * α x :=
  sorry

/-- Proper pushforward of a cycle, summing residue-weighted fibres of
`Points.map f`. -/
def properPushforwardCycle {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX)
    (α : Function.locallyFinsupp (Points X) ℤ) :
    Function.locallyFinsupp (Points Y) ℤ where
  toFun y :=
    ∑ᶠ x ∈ Points.map f ⁻¹' {y}, (mapCoeff pX pY δ f x : ℤ) * α x
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' y _ :=
    properPushforward_locallyFiniteSupport pX pY δ f hf α y

/-- Proper pushforward of cycles evaluates as the residue-weighted fibre sum. -/
theorem properPushforwardCycle_apply {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX)
    (α : Function.locallyFinsupp (Points X) ℤ) (y : Points Y) :
    properPushforwardCycle pX pY δ f hf α y =
      ∑ᶠ x ∈ Points.map f ⁻¹' {y}, (mapCoeff pX pY δ f x : ℤ) * α x :=
  rfl

/-- Proper pushforward preserves relative degree `k`. -/
theorem properPushforward_mem_cycleGroup {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX) (k : ℤ)
    {α : Function.locallyFinsupp (Points X) ℤ}
    (hα : α ∈ (cycleGroup pX) δ k) :
    properPushforwardCycle pX pY δ f hf α ∈ (cycleGroup pY) δ k :=
  sorry

/-- Proper pushforward sends the zero locally finite cycle to zero. -/
theorem properPushforwardCycle_zero {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX) :
    properPushforwardCycle pX pY δ f hf 0 = 0 :=
  sorry

/-- Proper pushforward preserves addition of locally finite cycles. -/
theorem properPushforwardCycle_add {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX)
    (α β : Function.locallyFinsupp (Points X) ℤ) :
    properPushforwardCycle pX pY δ f hf (α + β) =
      properPushforwardCycle pX pY δ f hf α +
        properPushforwardCycle pX pY δ f hf β :=
  sorry

/-- Proper pushforward as an additive map `Z_k(X) → Z_k(Y)`. -/
def properPushforwardHom {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX) (k : ℤ) :
    (cycleGroup pX) δ k →+ (cycleGroup pY) δ k where
  toFun α :=
    ⟨properPushforwardCycle pX pY δ f hf α,
      properPushforward_mem_cycleGroup pX pY δ f hf k α.property⟩
  map_zero' := by
    apply Subtype.ext
    exact properPushforwardCycle_zero pX pY δ f hf
  map_add' α β := by
    apply Subtype.ext
    exact properPushforwardCycle_add pX pY δ f hf α β

/-- The underlying cycle of the additive proper pushforward is the
residue-weighted pushforward of the underlying cycle. -/
theorem properPushforwardHom_apply {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX) (k : ℤ)
    (α : (cycleGroup pX) δ k) :
    (properPushforwardHom pX pY δ f hf k α).val =
      properPushforwardCycle pX pY δ f hf α :=
  rfl

/-- Proper pushforward of raw locally finite cycles is functorial in the
morphism. -/
theorem properPushforwardCycle_comp {S : Scheme.{u}}
    {B X Y Z : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pZ : Z ⟶ B) [QuasiSeparated pZ] [LocallyOfFiniteType pZ]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (g : Y ⟶ Z) [Proper g]
    (hf : f ≫ pY = pX) (hg : g ≫ pZ = pY)
    (α : Function.locallyFinsupp (Points X) ℤ) :
    properPushforwardCycle pY pZ δ g hg
        (properPushforwardCycle pX pY δ f hf α) =
      properPushforwardCycle pX pZ δ (f ≫ g) (by rw [Category.assoc, hg, hf])
        α :=
  sorry

/-- Successive proper pushforwards of cycles of relative dimension `k` equal
proper pushforward along the composite morphism. -/
theorem properPushforward_comp {S : Scheme.{u}} {B X Y Z : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pZ : Z ⟶ B) [QuasiSeparated pZ] [LocallyOfFiniteType pZ]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (g : Y ⟶ Z) [Proper g]
    (hf : f ≫ pY = pX) (hg : g ≫ pZ = pY) (k : ℤ) :
    (properPushforwardHom pY pZ δ g hg k).comp
        (properPushforwardHom pX pY δ f hf k) =
      properPushforwardHom pX pZ δ (f ≫ g) (by rw [Category.assoc, hg, hf])
        k :=
  sorry

open scoped Classical in
/-- The proper pushforward of the singleton cycle of an integral closed subspace
of relative dimension `k` is zero if its integral image has dimension less than
`k`, and otherwise is the residue degree at its generic point times the singleton
cycle of the image generic point. -/
theorem properPushforwardCycle_integralClosedSubspace
    {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX) (k : ℤ) [IsDecent Y]
    (Z : ClosedSubspace X) [IsIntegral Z.X]
    (hZ : AlgebraicGeometry.AlgebraicSpace.Hom.closedSubspaceDeltaDimension pX δ Z = (k : EInt)) :
    let ξ := Points.map Z.ι (ClosedSubspace.integralGenericPoint Z)
    properPushforwardCycle pX pY δ f hf
        (locallyFinsuppWithin.single ξ 1) =
      if AlgebraicGeometry.AlgebraicSpace.Hom.closedSubspaceDeltaDimension pY δ (Z.integralImage f) < (k : EInt) then
        0
      else
        (residueDegreeAlong pX pY f ξ : ℤ) •
          locallyFinsuppWithin.single
            (Points.map (Z.ι ≫ f) (ClosedSubspace.integralGenericPoint Z)) 1 :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
