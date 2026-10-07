module

public import ReasLib.AlgebraicGeometry.CycleGroup
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction.FlatBaseChange

/-!
# Flat base change of cycles of fixed dimension

This file defines the dimension-shifted pullback of cycles under flat base
change compatible with dimension functions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup

/-- The coefficient formula for dimension-shifted flat base change has locally
finite support. -/
theorem baseChangePullbackLocallyFiniteSupport
    {S S' X : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (f : X ⟶ S) [LocallyOfFiniteType f] (k : ℤ)
    (α : CycleGroup X (f.relativeDimensionFunction δ) k) :
    LocallyFiniteSupport (fun x' : (pullback f g : Scheme) ↦
      ∑ᶠ x : X,
        toAlgebraicCycle (f.relativeDimensionFunction δ) k α x *
          ((Scheme.IdealSheafData.associatedCycle
              ((Scheme.PointClosure.reducedStructure x).ideal.comap (pullback.fst f g))
              ((pullback.snd f g).relativeDimensionFunction δ') (k + c) :
                CycleGroup (pullback f g)
                  ((pullback.snd f g).relativeDimensionFunction δ') (k + c)) :
            AlgebraicCycle (pullback f g) ℤ) x') := sorry

/-- Every nonzero coefficient in the dimension-shifted flat-base-change
formula has relative `δ'`-dimension `k + c`. -/
theorem baseChangePullback_mem_dimensionSubgroup
    {S S' X : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (f : X ⟶ S) [LocallyOfFiniteType f] (k : ℤ)
    (α : CycleGroup X (f.relativeDimensionFunction δ) k) :
    ∀ x' : (pullback f g : Scheme),
      (∑ᶠ x : X,
        toAlgebraicCycle (f.relativeDimensionFunction δ) k α x *
          ((Scheme.IdealSheafData.associatedCycle
              ((Scheme.PointClosure.reducedStructure x).ideal.comap (pullback.fst f g))
              ((pullback.snd f g).relativeDimensionFunction δ') (k + c) :
                CycleGroup (pullback f g)
                  ((pullback.snd f g).relativeDimensionFunction δ') (k + c)) :
            AlgebraicCycle (pullback f g) ℤ) x') ≠ 0 →
        (pullback.snd f g).relativeDimensionFunction δ' x' = k + c := sorry

/-- The underlying value of dimension-shifted flat base change on a cycle. -/
noncomputable def baseChangePullbackValue
    {S S' X : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (f : X ⟶ S) [LocallyOfFiniteType f] (k : ℤ)
    (α : CycleGroup X (f.relativeDimensionFunction δ) k) :
    CycleGroup (pullback f g)
      ((pullback.snd f g).relativeDimensionFunction δ') (k + c) :=
  ⟨{ toFun := fun x' ↦
        ∑ᶠ x : X,
          toAlgebraicCycle (f.relativeDimensionFunction δ) k α x *
            ((Scheme.IdealSheafData.associatedCycle
                ((Scheme.PointClosure.reducedStructure x).ideal.comap (pullback.fst f g))
                ((pullback.snd f g).relativeDimensionFunction δ') (k + c) :
                  CycleGroup (pullback f g)
                    ((pullback.snd f g).relativeDimensionFunction δ') (k + c)) :
              AlgebraicCycle (pullback f g) ℤ) x'
     supportWithinDomain' := Set.subset_univ _
     supportLocallyFiniteWithinDomain' := fun x' _ ↦
       baseChangePullbackLocallyFiniteSupport g δ δ' c hcompat f k α x' },
    (AlgebraicCycle.mem_dimensionSubgroup
      ((pullback.snd f g).relativeDimensionFunction δ') (k + c) _).2
        (baseChangePullback_mem_dimensionSubgroup g δ δ' c hcompat f k α)⟩

/-- Dimension-shifted flat base change sends the zero cycle to zero. -/
theorem baseChangePullbackValue_zero
    {S S' X : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (f : X ⟶ S) [LocallyOfFiniteType f] (k : ℤ) :
    baseChangePullbackValue g δ δ' c hcompat f k 0 = 0 := sorry

/-- Dimension-shifted flat base change preserves addition of cycles. -/
theorem baseChangePullbackValue_add
    {S S' X : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (f : X ⟶ S) [LocallyOfFiniteType f] (k : ℤ)
    (a b : CycleGroup X (f.relativeDimensionFunction δ) k) :
    baseChangePullbackValue g δ δ' c hcompat f k (a + b) =
      baseChangePullbackValue g δ δ' c hcompat f k a +
        baseChangePullbackValue g δ δ' c hcompat f k b := sorry

/-- Flat base change compatible with `δ` and `δ'` up to `c` defines an
additive pullback from degree `k` cycles to degree `k + c` cycles. -/
noncomputable def baseChangePullback
    {S S' X : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (f : X ⟶ S) [LocallyOfFiniteType f] (k : ℤ) :
    CycleGroup X (f.relativeDimensionFunction δ) k →+
      CycleGroup (pullback f g)
        ((pullback.snd f g).relativeDimensionFunction δ') (k + c) where
  toFun := baseChangePullbackValue g δ δ' c hcompat f k
  map_zero' := baseChangePullbackValue_zero g δ δ' c hcompat f k
  map_add' := baseChangePullbackValue_add g δ δ' c hcompat f k

/-- The coefficient of a dimension-shifted flat base change is the sum of the
source coefficients times the cycles of inverse images of reduced point
closures. -/
theorem baseChangePullback_apply
    {S S' X : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (f : X ⟶ S) [LocallyOfFiniteType f] (k : ℤ)
    (α : CycleGroup X (f.relativeDimensionFunction δ) k)
    (x' : (pullback f g : Scheme)) :
    toAlgebraicCycle ((pullback.snd f g).relativeDimensionFunction δ') (k + c)
        (baseChangePullback g δ δ' c hcompat f k α) x' =
      ∑ᶠ x : X,
        toAlgebraicCycle (f.relativeDimensionFunction δ) k α x *
          ((Scheme.IdealSheafData.associatedCycle
              ((Scheme.PointClosure.reducedStructure x).ideal.comap (pullback.fst f g))
              ((pullback.snd f g).relativeDimensionFunction δ') (k + c) :
                CycleGroup (pullback f g)
                  ((pullback.snd f g).relativeDimensionFunction δ') (k + c)) :
            AlgebraicCycle (pullback f g) ℤ) x' := sorry

end AlgebraicGeometry.CycleGroup
