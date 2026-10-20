/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.CartierGysin
public import ReasLib.AlgebraicGeometry.BivariantClass.Descent
public import ReasLib.AlgebraicGeometry.ChowGroup.Reindex
public import ReasLib.AlgebraicGeometry.CycleGroup.Reindex
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Over
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Cap.Over
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.Operations
public import ReasLib.AlgebraicGeometry.RelativeCycle

/-!
# Bivariant class of a relative cycle

This file constructs the degree `-r` bivariant class attached to a relative
`r`-cycle, by descending the fibre-cycle action `g^*α ∩ -` through rational
equivalence.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.CyclesOnFibers

/-- Cycle-level cap family sending a cycle of `Y'` to the Chow class of
`g^*α ∩ β`, reindexed as a degree `-↑r` operation. -/
noncomputable def cycleCapFamily
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) (α : CyclesOnFibers f.left r) :
    BivariantClass.CycleCapFamily δ f (-(r : ℤ)) :=
  fun {X' _} _ _ _ f' _ _ square k ↦
    (AddEquiv.toAddMonoidHom
        (@ChowGroup.reindex X'.left
          (LocallyOfFiniteType.isLocallyNoetherian X'.hom)
          (X'.hom.relativeDimensionFunction δ) inferInstance
          (k + (r : ℤ)) (k - (-(r : ℤ)))
          (sub_neg_eq_add k (r : ℤ)).symm)).comp
      ((@chowClass X'.left (LocallyOfFiniteType.isLocallyNoetherian X'.hom)
          (X'.hom.relativeDimensionFunction δ) inferInstance
          (k + (r : ℤ))).comp
        ((CycleGroup.reindex (X'.hom.relativeDimensionFunction δ)
            (add_comm (r : ℤ) k)).comp
          (capOver δ f' (FiberCycleFamily.baseChange square α) k)))

/-- Evaluating `cycleCapFamily` recovers the Chow class of the transported
fibre-cycle action of the base-changed family. -/
theorem cycleCapFamily_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y X' Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) (r : ℕ) (α : CyclesOnFibers f.left r)
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (k : ℤ)
    (β : CycleGroup Y'.left (Y'.hom.relativeDimensionFunction δ) k) :
    cycleCapFamily δ f r α i f' g square k β =
      @ChowGroup.reindex X'.left
          (LocallyOfFiniteType.isLocallyNoetherian X'.hom)
          (X'.hom.relativeDimensionFunction δ) inferInstance
          (k + (r : ℤ)) (k - (-(r : ℤ)))
          (sub_neg_eq_add k (r : ℤ)).symm
        (@chowClass X'.left (LocallyOfFiniteType.isLocallyNoetherian X'.hom)
          (X'.hom.relativeDimensionFunction δ) inferInstance (k + (r : ℤ))
          (CycleGroup.reindex (X'.hom.relativeDimensionFunction δ)
            (add_comm (r : ℤ) k)
            (capOver δ f' (FiberCycleFamily.baseChange square α) k β))) :=
  sorry

end AlgebraicGeometry.Scheme.Hom.CyclesOnFibers

namespace AlgebraicGeometry.RelativeCycle

open AlgebraicGeometry.Scheme.Hom

/-- The cycle-level cap family of a relative cycle is compatible with
trivial-restriction effective-Cartier Gysin pullback. -/
theorem cycleCapFamily_compatibleWithTrivialCartierGysin
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsLocallyNoetherian Y.left]
    (r : ℕ) (α : CyclesOnFibers f.left r) (hα : IsRelative α) :
    BivariantClass.CompatibleWithTrivialCartierGysin δ (CyclesOnFibers.cycleCapFamily δ f r α) :=
  sorry

/-- The Chow-level cap family obtained by descending the fibre-cycle action of a
relative cycle through rational equivalence. -/
noncomputable def chowCapFamily
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsLocallyNoetherian Y.left]
    (r : ℕ) (α : CyclesOnFibers f.left r) (hα : IsRelative α) :
    BivariantClass.CapFamily δ f (-(r : ℤ)) :=
  BivariantClass.descend δ (CyclesOnFibers.cycleCapFamily δ f r α)
    (cycleCapFamily_compatibleWithTrivialCartierGysin δ f r α hα)

/-- The descended cap family of a relative cycle is compatible with proper
pushforward. -/
theorem chowCapFamily_mapProper
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsLocallyNoetherian Y.left]
    (r : ℕ) (α : CyclesOnFibers f.left r) (hα : IsRelative α) :
    BivariantClass.CompatibleWithProperPushforward δ (chowCapFamily δ f r α hα) :=
  sorry

/-- The descended cap family of a relative cycle is compatible with flat
pullback. -/
theorem chowCapFamily_pullbackFlat
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsLocallyNoetherian Y.left]
    (r : ℕ) (α : CyclesOnFibers f.left r) (hα : IsRelative α) :
    BivariantClass.CompatibleWithFlatPullback δ (chowCapFamily δ f r α hα) :=
  sorry

/-- The descended cap family of a relative cycle is compatible with
trivial-restriction effective-Cartier Gysin pullback on Chow groups. -/
theorem chowCapFamily_gysinTrivial
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsLocallyNoetherian Y.left]
    (r : ℕ) (α : CyclesOnFibers f.left r) (hα : IsRelative α) :
    BivariantClass.CompatibleWithTrivialCartierGysinOnChow δ
      (chowCapFamily δ f r α hα) :=
  sorry

/-- The degree `-r` bivariant class `c(α)` attached to a relative `r`-cycle. -/
noncomputable def bivariantClass
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsLocallyNoetherian Y.left]
    (r : ℕ) (α : CyclesOnFibers f.left r) (hα : IsRelative α) :
    AlgebraicGeometry.BivariantClass δ f (-(r : ℤ)) :=
  BivariantClass.ofTrivialCartierGysin δ f (-(r : ℤ))
    (chowCapFamily δ f r α hα)
    (chowCapFamily_mapProper δ f r α hα)
    (chowCapFamily_pullbackFlat δ f r α hα)
    (chowCapFamily_gysinTrivial δ f r α hα)

/-- The cap family of `bivariantClass` is the descended fibre-cycle action. -/
theorem bivariantClass_cap
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsLocallyNoetherian Y.left]
    (r : ℕ) (α : CyclesOnFibers f.left r) (hα : IsRelative α) :
    ((bivariantClass δ f r α hα).cap :
        BivariantClass.CapFamily δ f (-(r : ℤ))) =
      (chowCapFamily δ f r α hα :
        BivariantClass.CapFamily δ f (-(r : ℤ))) :=
  sorry

/-- A relative `r`-cycle defines a degree `-r` bivariant class whose action
on every cycle representative in a cartesian base change is the Chow class of
the base-changed fibre-cycle action, with the canonical degree transports. -/
theorem bivariantClass_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsLocallyNoetherian Y.left]
    (r : ℕ) (α : CyclesOnFibers f.left r) (hα : IsRelative α)
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (k : ℤ)
    (β : CycleGroup Y'.left (Y'.hom.relativeDimensionFunction δ) k) :
    (bivariantClass δ f r α hα).cap i f' g square k
        (@chowClass Y'.left (LocallyOfFiniteType.isLocallyNoetherian Y'.hom)
          (Y'.hom.relativeDimensionFunction δ) inferInstance k β) =
      @ChowGroup.reindex X'.left
          (LocallyOfFiniteType.isLocallyNoetherian X'.hom)
          (X'.hom.relativeDimensionFunction δ) inferInstance
          (k + (r : ℤ)) (k - (-(r : ℤ)))
          (sub_neg_eq_add k (r : ℤ)).symm
        (@chowClass X'.left (LocallyOfFiniteType.isLocallyNoetherian X'.hom)
          (X'.hom.relativeDimensionFunction δ) inferInstance (k + (r : ℤ))
          (CycleGroup.reindex (X'.hom.relativeDimensionFunction δ)
            (add_comm (r : ℤ) k)
            (CyclesOnFibers.capOver δ f'
              (FiberCycleFamily.baseChange square α) k β))) :=
  sorry


end AlgebraicGeometry.RelativeCycle
