module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Effective
public import ReasLib.AlgebraicGeometry.RelativeCycle.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.BaseChange

/-!
# Functoriality of relative cycles

Restriction, base change, flat pullback, and proper pushforward preserve
relativity and effectiveness of fibre-cycle families.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Restriction to a morphism of open subschemes preserves relative fibre-cycle families. -/
theorem isRelative_restrict {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ}
    {α : f.FiberCycleFamily r} (hα : IsRelative α) (U : X.Opens) (V : S.Opens)
    (φ : U.toScheme ⟶ V.toScheme) [LocallyOfFiniteType φ]
    (hφ : φ ≫ V.ι = U.ι ≫ f) :
    IsRelative (restrict U V φ hφ α) := sorry

/-- Flat pullback along a morphism of relative dimension `e` sends relative
`r`-cycle families to relative `(r + e)`-cycle families. -/
theorem isRelative_flatPullback {X' X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ}
    {α : f.FiberCycleFamily r} (hα : IsRelative α) (p : X' ⟶ X) (e : ℕ)
    [Flat p] [Scheme.Hom.RelativeDimension p e] :
    IsRelative (flatPullback p e α) := sorry

/-- Proper pushforward over a common base preserves relative `r`-cycle families. -/
theorem isRelative_properPushforward {X Y S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ}
    {α : f.FiberCycleFamily r} (hα : IsRelative α) (pY : Y ⟶ S)
    [LocallyOfFiniteType pY] (h : X ⟶ Y) [IsProper h] (hc : h ≫ pY = f) :
    IsRelative (pushforward pY h hc α) := sorry

/-- Restriction preserves effectiveness of relative fibre-cycle families. -/
theorem isEffective_restrict {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ}
    {α : f.FiberCycleFamily r} (hα : IsRelative α) (h_eff : IsEffective α)
    (U : X.Opens) (V : S.Opens) (φ : U.toScheme ⟶ V.toScheme)
    (hφ : φ ≫ V.ι = U.ι ≫ f) :
    @IsEffective _ _ φ (locallyOfFiniteType_restriction f U V φ hφ) _
      (restrict U V φ hφ α) := sorry

/-- Base change preserves effectiveness of relative fibre-cycle families. -/
theorem isEffective_baseChange {X S S' : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ}
    {α : f.FiberCycleFamily r} (hα : IsRelative α) (h_eff : IsEffective α)
    (g : S' ⟶ S) :
    IsEffective (FamilyOfCyclesOnFibres.baseChange f g r α) := sorry

/-- Flat pullback preserves effectiveness of relative fibre-cycle families. -/
theorem isEffective_flatPullback {X' X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ}
    {α : f.FiberCycleFamily r} (hα : IsRelative α) (h_eff : IsEffective α)
    (p : X' ⟶ X) (e : ℕ) [Flat p] [Scheme.Hom.RelativeDimension p e] :
    IsEffective (flatPullback p e α) := sorry

/-- Proper pushforward preserves effectiveness of relative fibre-cycle families. -/
theorem isEffective_pushforward {X Y S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ}
    {α : f.FiberCycleFamily r} (hα : IsRelative α) (h_eff : IsEffective α)
    (pY : Y ⟶ S) [LocallyOfFiniteType pY] (h : X ⟶ Y) [IsProper h]
    (hc : h ≫ pY = f) :
    IsEffective (pushforward pY h hc α) := sorry

end AlgebraicGeometry.RelativeCycle
