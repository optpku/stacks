module

public import ReasLib.AlgebraicGeometry.ChowGroup.FlatBaseChange
public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.Relative
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback.FlatBaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Dimension-shifted base change commutes with flat pullback on cycle groups. -/
#check (AlgebraicGeometry.CycleGroup.baseChangePullback_flatPullback :
  ∀ {S S' : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : Y ⟶ X) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (k : ℤ),
    (CycleGroup.reindex (((Over.pullback g).obj Y).hom.relativeDimensionFunction δ')
        (by
          rw [add_assoc k (r : ℤ) c, add_comm (r : ℤ) c,
            ← add_assoc k c (r : ℤ)])).comp
          ((CycleGroup.baseChangePullback g δ δ' c hcompat Y.hom (k + (r : ℤ))).comp
            (CycleGroup.flatPullback δ Y X f r k)) =
      (CycleGroup.flatPullback δ' ((Over.pullback g).obj Y) ((Over.pullback g).obj X)
          ((Over.pullback g).map f) r (k + c)).comp
        (CycleGroup.baseChangePullback g δ δ' c hcompat X.hom k))

/- Dimension-shifted base change sends rational boundaries to rational boundaries. -/
#check (AlgebraicGeometry.RationalEquivalence.baseChangePullback_mem_boundaries :
  ∀ {S S' X : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (f : X ⟶ S) [LocallyOfFiniteType f] (k : ℤ),
    @RationalEquivalence.boundaries X (LocallyOfFiniteType.isLocallyNoetherian f)
        (f.relativeDimensionFunction δ) inferInstance k ≤
      (@RationalEquivalence.boundaries (pullback f g)
        (LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f g))
        ((pullback.snd f g).relativeDimensionFunction δ') inferInstance (k + c)).comap
        (CycleGroup.baseChangePullback g δ δ' c hcompat f k))

/- Dimension-shifted flat base change defines an additive homomorphism on Chow groups. -/
#check (AlgebraicGeometry.ChowGroup.baseChangePullback :
  ∀ {S S' X : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (f : X ⟶ S) [LocallyOfFiniteType f] (k : ℤ),
    @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian f)
        (f.relativeDimensionFunction δ) inferInstance k →+
      @ChowGroup (pullback f g)
        (LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f g))
        ((pullback.snd f g).relativeDimensionFunction δ') inferInstance (k + c))

/- Chow-group base change is computed by cycle-level base change on representatives. -/
#check (AlgebraicGeometry.ChowGroup.baseChangePullback_chowClass :
  ∀ {S S' X : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (f : X ⟶ S) [LocallyOfFiniteType f] (k : ℤ)
    (α : CycleGroup X (f.relativeDimensionFunction δ) k),
    ChowGroup.baseChangePullback g δ δ' c hcompat f k
        (@chowClass X (LocallyOfFiniteType.isLocallyNoetherian f)
          (f.relativeDimensionFunction δ) inferInstance k α) =
      @chowClass (pullback f g)
        (LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f g))
        ((pullback.snd f g).relativeDimensionFunction δ') inferInstance (k + c)
        (CycleGroup.baseChangePullback g δ δ' c hcompat f k α))

/- Dimension-shifted base change commutes with flat pullback on Chow groups. -/
#check (AlgebraicGeometry.ChowGroup.baseChangePullback_flatPullback :
  ∀ {S S' : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : Y ⟶ X) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (k : ℤ),
    (@ChowGroup.reindex ((Over.pullback g).obj Y).left
        (@LocallyOfFiniteType.isLocallyNoetherian _ _ ((Over.pullback g).obj Y).hom
          (LocallyOfFiniteType.instOverPullbackObj g Y) inferInstance)
        (((Over.pullback g).obj Y).hom.relativeDimensionFunction δ') inferInstance
        ((k + (r : ℤ)) + c) ((k + c) + (r : ℤ))
        (by
          rw [add_assoc k (r : ℤ) c, add_comm (r : ℤ) c,
            ← add_assoc k c (r : ℤ)])).toAddMonoidHom.comp
          ((ChowGroup.baseChangePullback g δ δ' c hcompat Y.hom (k + (r : ℤ))).comp
            (ChowGroup.flatPullback δ Y X f r k)) =
      (ChowGroup.flatPullback δ' ((Over.pullback g).obj Y) ((Over.pullback g).obj X)
          ((Over.pullback g).map f) r (k + c)).comp
        (ChowGroup.baseChangePullback g δ δ' c hcompat X.hom k))
