module

public import ReasLib.AlgebraicGeometry.Scheme.Pullback.OverMap
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Cap
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.Operations
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback.Along
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Pullback

/-!
# Compatibility of the fibre-cycle action with flat base change

The action of a family of fibre cycles commutes with dimension-shifted flat base
change and with flat pullback along a morphism of fixed relative dimension.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.CyclesOnFibers

/-- The action of a family of fibre cycles on a cycle commutes with
dimension-shifted flat base change. -/
theorem cap_baseChange {S S' X Y : Scheme.{u}}
    [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    {r e : ℤ} (α : CyclesOnFibers f r)
    (β : CycleGroup Y (p.relativeDimensionFunction δ) e) :
    CycleGroup.toAlgebraicCycle
        ((Scheme.Pullback.overMap g p f ≫ pullback.snd p g).relativeDimensionFunction δ')
        (r + (e + c))
        (cap (pullback.snd p g) (Scheme.Pullback.overMap g p f) δ'
          (FiberCycleFamily.baseChange (Scheme.Pullback.isPullback_overMap g p f) α)
          (CycleGroup.baseChangePullback g δ δ' c hcompat p e β)) =
      CycleGroup.toAlgebraicCycle
        ((pullback.snd (f ≫ p) g).relativeDimensionFunction δ')
        ((r + e) + c)
        (CycleGroup.baseChangePullback g δ δ' c hcompat (f ≫ p) (r + e)
          (cap p f δ α β)) :=
    sorry

/-- Evaluating `cap_baseChange` at a point of `X ×_S S'` compares the
coefficients of both underlying algebraic cycles. -/
theorem cap_baseChange_apply {S S' X Y : Scheme.{u}}
    [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    {r e : ℤ} (α : CyclesOnFibers f r)
    (β : CycleGroup Y (p.relativeDimensionFunction δ) e)
    (x' : (pullback (f ≫ p) g : Scheme)) :
    CycleGroup.toAlgebraicCycle
        ((Scheme.Pullback.overMap g p f ≫ pullback.snd p g).relativeDimensionFunction δ')
        (r + (e + c))
        (cap (pullback.snd p g) (Scheme.Pullback.overMap g p f) δ'
          (FiberCycleFamily.baseChange (Scheme.Pullback.isPullback_overMap g p f) α)
          (CycleGroup.baseChangePullback g δ δ' c hcompat p e β)) x' =
      CycleGroup.toAlgebraicCycle
        ((pullback.snd (f ≫ p) g).relativeDimensionFunction δ')
        ((r + e) + c)
        (CycleGroup.baseChangePullback g δ δ' c hcompat (f ≫ p) (r + e)
          (cap p f δ α β)) x' := by
  exact congrArg (fun γ : AlgebraicCycle _ ℤ ↦ γ x')
    (cap_baseChange g δ δ' c hcompat p f α β)

/-- The action of a family of fibre cycles on a cycle commutes with flat
pullback along a morphism of fixed relative dimension. -/
theorem cap_flatPullback {S X Y Y' : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (p : Y ⟶ S) (f : X ⟶ Y)
    (h : Y' ⟶ Y) (c : ℕ) [Flat h] [RelativeDimension h c]
    [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    {r e : ℤ} (α : CyclesOnFibers f r)
    (β : CycleGroup Y (p.relativeDimensionFunction δ) e) :
    CycleGroup.toAlgebraicCycle
        ((pullback.snd f h ≫ h ≫ p).relativeDimensionFunction δ)
        (r + (e + (c : ℤ)))
        (cap (h ≫ p) (pullback.snd f h) δ
          (FiberCycleFamily.baseChange (IsPullback.of_hasPullback f h) α)
          (CycleGroup.flatPullbackAlong δ (h ≫ p) p h rfl c e β)) =
      CycleGroup.toAlgebraicCycle
        ((pullback.fst f h ≫ f ≫ p).relativeDimensionFunction δ)
        ((r + e) + (c : ℤ))
        (CycleGroup.flatPullbackAlong δ (pullback.fst f h ≫ f ≫ p)
          (f ≫ p) (pullback.fst f h) rfl c (r + e) (cap p f δ α β)) :=
    sorry

/-- Evaluating `cap_flatPullback` at a point of `X ×_Y Y'` compares the
coefficients of both underlying algebraic cycles. -/
theorem cap_flatPullback_apply {S X Y Y' : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (p : Y ⟶ S) (f : X ⟶ Y)
    (h : Y' ⟶ Y) (c : ℕ) [Flat h] [RelativeDimension h c]
    [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    {r e : ℤ} (α : CyclesOnFibers f r)
    (β : CycleGroup Y (p.relativeDimensionFunction δ) e)
    (x' : (pullback f h : Scheme)) :
    CycleGroup.toAlgebraicCycle
        ((pullback.snd f h ≫ h ≫ p).relativeDimensionFunction δ)
        (r + (e + (c : ℤ)))
        (cap (h ≫ p) (pullback.snd f h) δ
          (FiberCycleFamily.baseChange (IsPullback.of_hasPullback f h) α)
          (CycleGroup.flatPullbackAlong δ (h ≫ p) p h rfl c e β)) x' =
      CycleGroup.toAlgebraicCycle
        ((pullback.fst f h ≫ f ≫ p).relativeDimensionFunction δ)
        ((r + e) + (c : ℤ))
        (CycleGroup.flatPullbackAlong δ (pullback.fst f h ≫ f ≫ p)
          (f ≫ p) (pullback.fst f h) rfl c (r + e) (cap p f δ α β)) x' := by
  exact congrArg (fun γ : AlgebraicCycle _ ℤ ↦ γ x')
    (cap_flatPullback δ p f h c α β)


end AlgebraicGeometry.Scheme.Hom.CyclesOnFibers
