module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Functoriality
public import ReasLib.AlgebraicGeometry.RelativeCycle.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Cover.H.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Cover.H.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Cover.H.Stability

/-!
# Descent of relative cycles along h coverings

Relativity of a fibre-cycle family can be checked after base change along
every member of an h covering of a locally Noetherian base.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace AlgebraicGeometry.RelativeCycle

/-- Base change of a relative `r`-cycle along every member of an h covering
of a locally Noetherian base remains a relative `r`-cycle. -/
theorem isRelative_hCovering_baseChange {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ) (α : f.FiberCycleFamily r)
    {ι : Type v} (family : ι → Over S) [Scheme.HCovering family] :
    IsRelative α →
      ∀ i, IsRelative (FamilyOfCyclesOnFibres.baseChange f (family i).hom r α) := sorry

/-- A fibre-cycle family over a locally Noetherian base is relative if its
base change along every member of an h covering is relative. -/
theorem isRelative_of_hCovering_baseChange {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ) (α : f.FiberCycleFamily r)
    {ι : Type v} (family : ι → Over S) [Scheme.HCovering family] :
    (∀ i, IsRelative (FamilyOfCyclesOnFibres.baseChange f (family i).hom r α)) →
      IsRelative α := sorry

/-- For a locally finite type morphism over a locally Noetherian base, a
fibre-cycle family is relative exactly when its base change along every member
of an h covering is relative. -/
theorem isRelative_iff_hCovering_baseChange {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ) (α : f.FiberCycleFamily r)
    {ι : Type v} (family : ι → Over S) [Scheme.HCovering family] :
    IsRelative α ↔
      ∀ i, IsRelative (FamilyOfCyclesOnFibres.baseChange f (family i).hom r α) := sorry

/-- A fibre-cycle family for a locally finite type morphism over a locally
Noetherian base belongs to the relative-cycle subgroup exactly when all its
base changes along an h covering belong to the respective relative-cycle subgroups. -/
theorem mem_group_iff_hCovering_baseChange {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ) (α : f.FiberCycleFamily r)
    {ι : Type v} (family : ι → Over S) [Scheme.HCovering family] :
    α ∈ group f r ↔
      ∀ i, FamilyOfCyclesOnFibres.baseChange f (family i).hom r α ∈
        group (pullback.snd f (family i).hom) r := sorry

end AlgebraicGeometry.RelativeCycle
