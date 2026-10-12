/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup.FlatBaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- The locally finite support statement for the dimension-shifted base-change
coefficient formula. -/
#check (AlgebraicGeometry.CycleGroup.baseChangePullbackLocallyFiniteSupport :
  ∀ {S S' X : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (f : X ⟶ S) [LocallyOfFiniteType f] (k : ℤ)
    (α : CycleGroup X (f.relativeDimensionFunction δ) k),
    LocallyFiniteSupport (fun x' : (pullback f g : Scheme) ↦
      ∑ᶠ x : X,
        CycleGroup.toAlgebraicCycle (f.relativeDimensionFunction δ) k α x *
          ((Scheme.IdealSheafData.associatedCycle
              ((Scheme.PointClosure.reducedStructure x).ideal.comap (pullback.fst f g))
              ((pullback.snd f g).relativeDimensionFunction δ') (k + c) :
                CycleGroup (pullback f g)
                  ((pullback.snd f g).relativeDimensionFunction δ') (k + c)) :
            AlgebraicCycle (pullback f g) ℤ) x'))

/- The grading statement for the dimension-shifted base-change coefficient
formula. -/
#check (AlgebraicGeometry.CycleGroup.baseChangePullback_mem_dimensionSubgroup :
  ∀ {S S' X : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (f : X ⟶ S) [LocallyOfFiniteType f] (k : ℤ)
    (α : CycleGroup X (f.relativeDimensionFunction δ) k)
    (x' : (pullback f g : Scheme)),
    (∑ᶠ x : X,
      CycleGroup.toAlgebraicCycle (f.relativeDimensionFunction δ) k α x *
        ((Scheme.IdealSheafData.associatedCycle
            ((Scheme.PointClosure.reducedStructure x).ideal.comap (pullback.fst f g))
            ((pullback.snd f g).relativeDimensionFunction δ') (k + c) :
              CycleGroup (pullback f g)
                ((pullback.snd f g).relativeDimensionFunction δ') (k + c)) :
          AlgebraicCycle (pullback f g) ℤ) x') ≠ 0 →
      (pullback.snd f g).relativeDimensionFunction δ' x' = k + c)

/- The additive dimension-shifted pullback on cycle groups. -/
#check (AlgebraicGeometry.CycleGroup.baseChangePullback :
  ∀ {S S' X : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (f : X ⟶ S) [LocallyOfFiniteType f] (k : ℤ),
    CycleGroup X (f.relativeDimensionFunction δ) k →+
      CycleGroup (pullback f g)
        ((pullback.snd f g).relativeDimensionFunction δ') (k + c))

/- The coefficient formula for the additive dimension-shifted pullback. -/
#check (AlgebraicGeometry.CycleGroup.baseChangePullback_apply :
  ∀ {S S' X : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (f : X ⟶ S) [LocallyOfFiniteType f] (k : ℤ)
    (α : CycleGroup X (f.relativeDimensionFunction δ) k)
    (x' : (pullback f g : Scheme)),
    CycleGroup.toAlgebraicCycle
        ((pullback.snd f g).relativeDimensionFunction δ') (k + c)
        (CycleGroup.baseChangePullback g δ δ' c hcompat f k α) x' =
      ∑ᶠ x : X,
        CycleGroup.toAlgebraicCycle (f.relativeDimensionFunction δ) k α x *
          ((Scheme.IdealSheafData.associatedCycle
              ((Scheme.PointClosure.reducedStructure x).ideal.comap (pullback.fst f g))
              ((pullback.snd f g).relativeDimensionFunction δ') (k + c) :
                CycleGroup (pullback f g)
                  ((pullback.snd f g).relativeDimensionFunction δ') (k + c)) :
            AlgebraicCycle (pullback f g) ℤ) x')
