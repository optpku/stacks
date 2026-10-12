/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.LocallyFiniteSum
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.MeromorphicSection
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback

@[expose] public section

open CategoryTheory Function Set Topology
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry

namespace WeilDivisor

/-- The singleton cycles obtained from the coefficients of a divisor on a reduced point
closure form a locally finite family on the ambient scheme. -/
theorem pointClosureTermsLocallyFinite {X : Scheme.{u}} (x : X)
    (D : Div(Scheme.PointClosure.scheme x)) :
    LocallyFinite fun Z : PrimeDivisor (Scheme.PointClosure.scheme x) ↦
      (@Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _
        ((Scheme.PointClosure.ι x).base Z.genericPoint) (D.coeff Z)).support := sorry

/-- The pushed-forward cycle of a divisor on the reduced closure of a degree-`k + 1` point
is supported in degree `k`. -/
theorem pointClosureCycle_mem {X : Scheme.{u}} [IsLocallyNoetherian X]
    (d : X → ℤ) [IsDimensionFunction d] (k : ℤ) (x : X) (hx : d x = k + 1)
    (D : Div(Scheme.PointClosure.scheme x)) :
    AlgebraicCycle.locallyFiniteSum
      (fun Z : PrimeDivisor (Scheme.PointClosure.scheme x) ↦
        @Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _
          ((Scheme.PointClosure.ι x).base Z.genericPoint) (D.coeff Z))
      (pointClosureTermsLocallyFinite x D) ∈
        AlgebraicCycle.dimensionSubgroup d k := sorry

/-- The degree-`k` cycle on `X` obtained by pushing a divisor on the reduced closure of a
degree-`k + 1` point into `X`. -/
noncomputable def pointClosureCycle {X : Scheme.{u}} [IsLocallyNoetherian X]
    (d : X → ℤ) [IsDimensionFunction d] (k : ℤ) (x : X) (hx : d x = k + 1)
    (D : Div(Scheme.PointClosure.scheme x)) : CycleGroup X d k :=
  ⟨AlgebraicCycle.locallyFiniteSum
      (fun Z : PrimeDivisor (Scheme.PointClosure.scheme x) ↦
        @Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _
          ((Scheme.PointClosure.ι x).base Z.genericPoint) (D.coeff Z))
      (pointClosureTermsLocallyFinite x D),
    pointClosureCycle_mem d k x hx D⟩

/-- The pushed-forward divisor cycle is supported on the closure of its source point. -/
theorem pointClosureCycle_support {X : Scheme.{u}} [IsLocallyNoetherian X]
    (d : X → ℤ) [IsDimensionFunction d] (k : ℤ) (x : X) (hx : d x = k + 1)
    (D : Div(Scheme.PointClosure.scheme x)) :
    (CycleGroup.toAlgebraicCycle d k (pointClosureCycle d k x hx D)).support ⊆
      (Scheme.PointClosure.closedSubset x : Set X) := sorry

/-- Pushing linearly equivalent divisors from a reduced point closure gives the same Chow
class on the ambient scheme. -/
theorem pointClosureCycle_chowClass_eq {X : Scheme.{u}} [IsLocallyNoetherian X]
    (d : X → ℤ) [IsDimensionFunction d] (k : ℤ) (x : X) (hx : d x = k + 1)
    (D E : Div(Scheme.PointClosure.scheme x))
    (hDE : weilDivisorClassGroupMk (Scheme.PointClosure.scheme x) D =
      weilDivisorClassGroupMk (Scheme.PointClosure.scheme x) E) :
    chowClass d k (pointClosureCycle d k x hx D) =
      chowClass d k (pointClosureCycle d k x hx E) := sorry

end WeilDivisor

namespace Scheme

/-- The concrete Weil divisor selected by the canonical regular meromorphic section of an
invertible module on an integral locally Noetherian scheme. -/
noncomputable def invertibleModuleWeilDivisor (X : Scheme.{u}) [IsLocallyNoetherian X]
    [IsIntegral X] (ℒ : X.Modules) [Modules.Invertible ℒ] : Div(X) :=
  nonzeroMeromorphicSectionWeilDivisor X ℒ
    (Modules.Invertible.regularMeromorphicSection ℒ)
    (Modules.Invertible.regularMeromorphicSection_ne_zero ℒ)

/-- The class of the concrete divisor selected for an invertible module is its canonical
invertible-module Weil divisor class. -/
theorem invertibleModuleWeilDivisor_class (X : Scheme.{u}) [IsLocallyNoetherian X]
    [IsIntegral X] (ℒ : X.Modules) [Modules.Invertible ℒ] :
    weilDivisorClassGroupMk X (invertibleModuleWeilDivisor X ℒ) =
      invertibleModuleWeilDivisorClass X ℒ := sorry

namespace Modules

/-- The degree-`k` cycle contributed by a degree-`k + 1` point to intersection with the first
Chern class of an invertible module. -/
noncomputable def firstChernGeneratorCycle {X : Scheme.{u}} [IsLocallyNoetherian X]
    (d : X → ℤ) [IsDimensionFunction d] (ℒ : X.Modules) [Invertible ℒ]
    (k : ℤ) (x : X) (hx : d x = k + 1) : CycleGroup X d k :=
  WeilDivisor.pointClosureCycle d k x hx
    (Scheme.invertibleModuleWeilDivisor (Scheme.PointClosure.scheme x)
      ((pullback (Scheme.PointClosure.ι x)).obj ℒ))

/-- A first-Chern generator cycle is supported on the closure of its source point. -/
theorem firstChernGeneratorCycle_support {X : Scheme.{u}} [IsLocallyNoetherian X]
    (d : X → ℤ) [IsDimensionFunction d] (ℒ : X.Modules) [Invertible ℒ]
    (k : ℤ) (x : X) (hx : d x = k + 1) :
    (CycleGroup.toAlgebraicCycle d k
      (firstChernGeneratorCycle d ℒ k x hx)).support ⊆
        (Scheme.PointClosure.closedSubset x : Set X) := sorry

/-- The first-Chern generator terms selected by a degree-`k + 1` cycle form a locally finite
family of degree-`k` cycles. -/
theorem firstChernGeneratorTermsLocallyFinite {X : Scheme.{u}} [IsLocallyNoetherian X]
    (d : X → ℤ) [IsDimensionFunction d] (ℒ : X.Modules) [Invertible ℒ]
    (k : ℤ) (α : CycleGroup X d (k + 1)) :
    LocallyFinite fun x : X ↦
      (CycleGroup.toAlgebraicCycle d k
        (if hx : d x = k + 1 then
          (CycleGroup.toAlgebraicCycle d (k + 1) α x) •
            firstChernGeneratorCycle d ℒ k x hx
        else 0)).support := sorry

/-- The cycle representative obtained by extending first-Chern intersection from integral
point closures to an arbitrary degree-`k + 1` cycle. -/
noncomputable def firstChernCycle {X : Scheme.{u}} [IsLocallyNoetherian X]
    (d : X → ℤ) [IsDimensionFunction d] (ℒ : X.Modules) [Invertible ℒ]
    (k : ℤ) (α : CycleGroup X d (k + 1)) : CycleGroup X d k :=
  CycleGroup.locallyFiniteSum d k
    (fun x : X ↦
      if hx : d x = k + 1 then
        (CycleGroup.toAlgebraicCycle d (k + 1) α x) •
          firstChernGeneratorCycle d ℒ k x hx
      else 0)
    (firstChernGeneratorTermsLocallyFinite d ℒ k α)

/-- The Chow class of the first-Chern cycle representative vanishes on the zero cycle. -/
theorem firstChernCycleClass_zero {X : Scheme.{u}} [IsLocallyNoetherian X]
    (d : X → ℤ) [IsDimensionFunction d] (ℒ : X.Modules) [Invertible ℒ] (k : ℤ) :
    chowClass d k (firstChernCycle d ℒ k 0) = 0 := sorry

/-- Taking the Chow class of the first-Chern cycle representative preserves addition. -/
theorem firstChernCycleClass_add {X : Scheme.{u}} [IsLocallyNoetherian X]
    (d : X → ℤ) [IsDimensionFunction d] (ℒ : X.Modules) [Invertible ℒ]
    (k : ℤ) (α β : CycleGroup X d (k + 1)) :
    chowClass d k (firstChernCycle d ℒ k (α + β)) =
      chowClass d k (firstChernCycle d ℒ k α) +
        chowClass d k (firstChernCycle d ℒ k β) := sorry

/-- Intersection with the first Chern class of an invertible module, as an additive map from
degree-`k + 1` cycles to degree-`k` Chow classes. -/
noncomputable def firstChernClassCapOfDimension {X : Scheme.{u}} [IsLocallyNoetherian X]
    (d : X → ℤ) [IsDimensionFunction d] (ℒ : X.Modules) [Invertible ℒ] (k : ℤ) :
    CycleGroup X d (k + 1) →+ ChowGroup X d k where
  toFun := fun α ↦ chowClass d k (firstChernCycle d ℒ k α)
  map_zero' := firstChernCycleClass_zero d ℒ k
  map_add' := firstChernCycleClass_add d ℒ k

/-- Intersection with the first Chern class, using the relative dimension function induced
from a universally catenary base. -/
noncomputable def firstChernClassCap {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (ℒ : X.Modules) [Invertible ℒ] (k : ℤ) :
    CycleGroup X (p.relativeDimensionFunction δ) (k + 1) →+
      @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k :=
  @firstChernClassCapOfDimension X (LocallyOfFiniteType.isLocallyNoetherian p)
    (p.relativeDimensionFunction δ) inferInstance ℒ inferInstance k

/-- The relative first-Chern cap map is computed by the explicit locally finite cycle
construction before passage to the Chow quotient. -/
theorem firstChernClassCap_apply {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (ℒ : X.Modules) [Invertible ℒ]
    (k : ℤ) (α : CycleGroup X (p.relativeDimensionFunction δ) (k + 1)) :
    firstChernClassCap p δ ℒ k α =
      @chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k
        (@firstChernCycle X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) inferInstance ℒ inferInstance k α) := sorry

/-- First-Chern intersection is additive with respect to tensor products of invertible
modules. -/
theorem firstChernClassCap_tensor {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)
    (ℒ 𝒩 : X.Modules) [Invertible ℒ] [Invertible 𝒩]
    (α : CycleGroup X (p.relativeDimensionFunction δ) (k + 1)) :
    firstChernClassCap p δ ℒ k α + firstChernClassCap p δ 𝒩 k α =
      firstChernClassCap p δ (ℒ ⊗ 𝒩) k α := sorry

/-- First-Chern intersection with the tensor unit is zero. -/
theorem firstChernClassCap_tensorUnit {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) (k + 1)) :
    firstChernClassCap p δ (𝟙_ X.Modules) k α = 0 := sorry

end Modules

end Scheme

end AlgebraicGeometry
