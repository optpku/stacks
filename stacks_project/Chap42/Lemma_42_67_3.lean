module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatBaseChange.AssociatedCycle

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 42.67.3 (1): flat base change compatible with dimension functions up
to `c` sends a closed subscheme of relative `δ`-dimension at most `k` to one
of relative `δ'`-dimension at most `k + c`. -/
@[stacks 0FVI] #check
  (AlgebraicGeometry.Scheme.Hom.closedSubschemeDeltaDimension_baseChange_le :
  ∀ {S S' X : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (f : X ⟶ S) [LocallyOfFiniteType f] (Z : X.IdealSheafData) (k : ℤ)
    (hZ : f.closedSubschemeDeltaDimension δ Z ≤ (k : EInt)),
    (pullback.snd f g).closedSubschemeDeltaDimension δ'
        (Z.comap (pullback.fst f g)) ≤ ((k + c : ℤ) : EInt))

/- Lemma 42.67.3 (2): the degree-`k + c` cycle of a base-changed closed
subscheme is the dimension-shifted flat pullback of its degree-`k` cycle. -/
@[stacks 0FVI] #check
  (AlgebraicGeometry.CycleGroup.baseChangePullback_closedSubschemeCycle :
  ∀ {S S' X : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (f : X ⟶ S) [LocallyOfFiniteType f] (Z : X.IdealSheafData) (k : ℤ)
    (hZ : f.closedSubschemeDeltaDimension δ Z ≤ (k : EInt)),
    (pullback.snd f g).closedSubschemeCycle δ' (Z.comap (pullback.fst f g))
        (k + c) (Scheme.Hom.closedSubschemeDeltaDimension_baseChange_le
          g δ δ' c hcompat f Z k hZ) =
      CycleGroup.baseChangePullback g δ δ' c hcompat f k
        (f.closedSubschemeCycle δ Z k hZ))

/- Lemma 42.67.3 (3): flat base change compatible with dimension functions up
to `c` sends the support of a coherent module of relative `δ`-dimension at
most `k` to support of relative `δ'`-dimension at most `k + c`. -/
@[stacks 0FVI] #check
  (AlgebraicGeometry.Scheme.Modules.pullbackSupportDeltaDimension_baseChange_le :
  ∀ {S S' X : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent] (k : ℤ)
    (hF : f.closedSubschemeDeltaDimension δ
      (Scheme.Modules.schemeTheoreticSupport F) ≤ (k : EInt)),
    (pullback.snd f g).closedSubschemeDeltaDimension δ'
        (Scheme.Modules.schemeTheoreticSupport
          ((Scheme.Modules.pullback (pullback.fst f g)).obj F)) ≤
      ((k + c : ℤ) : EInt))

/- Lemma 42.67.3 (4): dimension-shifted flat pullback carries the degree-`k`
associated cycle of a coherent module to the degree-`k + c` associated cycle
of its base change. -/
@[stacks 0FVI] #check
  (AlgebraicGeometry.Scheme.Modules.associatedCycle_baseChange :
  ∀ {S S' X : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent] (k : ℤ)
    (hF : f.closedSubschemeDeltaDimension δ
      (Scheme.Modules.schemeTheoreticSupport F) ≤ (k : EInt)),
    CycleGroup.baseChangePullback g δ δ' c hcompat f k
        (Scheme.Modules.relativeAssociatedCycle f δ F k) =
      Scheme.Modules.relativeAssociatedCycle
        (hF := @Scheme.Modules.pullback_isCoherent
          (CategoryTheory.Limits.pullback f g) X
          (LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f g))
          (LocallyOfFiniteType.isLocallyNoetherian f) (pullback.fst f g) F inferInstance)
        (pullback.snd f g) δ'
        ((Scheme.Modules.pullback (pullback.fst f g)).obj F) (k + c))
