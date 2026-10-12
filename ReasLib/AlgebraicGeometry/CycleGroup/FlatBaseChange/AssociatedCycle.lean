/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup.FlatBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.StructureSheafCycle
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport

/-!
# Associated cycles under flat base change

This file records dimension bounds and associated-cycle formulas for coherent
modules and closed subschemes under dimension-shifted flat base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

namespace Scheme.Modules

/-- Flat base change compatible with dimension functions up to `c` sends the
support of a coherent module of relative `δ`-dimension at most `k` to support
of relative `δ'`-dimension at most `k + c`. -/
theorem pullbackSupportDeltaDimension_baseChange_le
    {S S' X : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent] (k : ℤ)
    (hF : f.closedSubschemeDeltaDimension δ (schemeTheoreticSupport F) ≤ (k : EInt)) :
    (pullback.snd f g).closedSubschemeDeltaDimension δ'
        (schemeTheoreticSupport ((Scheme.Modules.pullback (pullback.fst f g)).obj F)) ≤
      ((k + c : ℤ) : EInt) := sorry

/-- Dimension-shifted flat base change carries the degree-`k` associated cycle
of a coherent module to the degree-`k + c` associated cycle of its pullback. -/
theorem associatedCycle_baseChange
    {S S' X : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent] (k : ℤ)
    (hF : f.closedSubschemeDeltaDimension δ (schemeTheoreticSupport F) ≤ (k : EInt)) :
    CycleGroup.baseChangePullback g δ δ' c hcompat f k
        (relativeAssociatedCycle f δ F k) =
      relativeAssociatedCycle
        (hF := @pullback_isCoherent (CategoryTheory.Limits.pullback f g) X
          (LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f g))
          (LocallyOfFiniteType.isLocallyNoetherian f) (pullback.fst f g) F inferInstance)
        (pullback.snd f g) δ'
        ((Scheme.Modules.pullback (pullback.fst f g)).obj F) (k + c) := sorry

end Scheme.Modules

namespace Scheme.Hom

/-- Flat base change compatible with dimension functions up to `c` sends a
closed subscheme of relative `δ`-dimension at most `k` to one of relative
`δ'`-dimension at most `k + c`. -/
theorem closedSubschemeDeltaDimension_baseChange_le
    {S S' X : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (f : X ⟶ S) [LocallyOfFiniteType f] (Z : X.IdealSheafData) (k : ℤ)
    (hZ : f.closedSubschemeDeltaDimension δ Z ≤ (k : EInt)) :
    (pullback.snd f g).closedSubschemeDeltaDimension δ'
        (Z.comap (pullback.fst f g)) ≤ ((k + c : ℤ) : EInt) := sorry

end Scheme.Hom

namespace CycleGroup

/-- The degree-`k + c` cycle of a base-changed closed subscheme is the
dimension-shifted flat pullback of its degree-`k` cycle. -/
theorem baseChangePullback_closedSubschemeCycle
    {S S' X : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (f : X ⟶ S) [LocallyOfFiniteType f] (Z : X.IdealSheafData) (k : ℤ)
    (hZ : f.closedSubschemeDeltaDimension δ Z ≤ (k : EInt)) :
    (pullback.snd f g).closedSubschemeCycle δ' (Z.comap (pullback.fst f g))
        (k + c) (Scheme.Hom.closedSubschemeDeltaDimension_baseChange_le
          g δ δ' c hcompat f Z k hZ) =
      baseChangePullback g δ δ' c hcompat f k
        (f.closedSubschemeCycle δ Z k hZ) := sorry

end CycleGroup

end AlgebraicGeometry
