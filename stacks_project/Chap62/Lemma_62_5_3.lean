module

public import stacks_project.Chap62.Example_62_5_2_AssociatedCycle
public import stacks_project.Chap62.Lemma_62_5_1_Operations

/-!
# Compatibility of associated module cycle families

The associated fibrewise cycle family of a quasi-coherent finite-type module
commutes with base change, restriction, and flat pullback.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The fibrewise support-dimension bound is preserved by pullback of the module
along a cartesian square. -/
theorem fiberModuleSupportDimensionLE_baseChange
    {S X S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (hpb : IsPullback g' f' f g)
    (F : X.Modules) (r : ℕ) (hF : f.fiberModuleSupportDimensionLE F r) :
    f'.fiberModuleSupportDimensionLE ((Modules.pullback g').obj F) r := sorry

/-- Lemma 62.5.3 (1): the associated fibrewise cycle family of a quasi-coherent
finite-type module commutes with base change along a cartesian square. -/
@[stacks 0H4R]
theorem moduleFiberCycleFamily_baseChange
    {S X S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (hpb : IsPullback g' f' f g)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (r : ℕ)
    (hF : f.fiberModuleSupportDimensionLE F r) :
    FiberCycleFamily.baseChange hpb (moduleFiberCycleFamily f F r hF) =
      moduleFiberCycleFamily f' ((Modules.pullback g').obj F) r
        (fiberModuleSupportDimensionLE_baseChange hpb F r hF) := sorry

/-- The fibrewise support-dimension bound is preserved by restriction to
compatible opens. -/
theorem fiberModuleSupportDimensionLE_restrict
    {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
    (U : X.Opens) (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V) (F : X.Modules) (r : ℕ)
    (hF : f.fiberModuleSupportDimensionLE F r) :
    (f.resLE V U hU).fiberModuleSupportDimensionLE
      ((Modules.pullback U.ι).obj F) r := sorry

/-- Lemma 62.5.3 (2): the associated fibrewise cycle family of a quasi-coherent
finite-type module commutes with restriction to compatible opens. -/
@[stacks 0H4R]
theorem moduleFiberCycleFamily_restrict
    {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
    (U : X.Opens) (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V) (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (r : ℕ)
    (hF : f.fiberModuleSupportDimensionLE F r) :
    FiberCycleFamily.restrict U V hU (moduleFiberCycleFamily f F r hF) =
      moduleFiberCycleFamily (f.resLE V U hU) ((Modules.pullback U.ι).obj F) r
        (fiberModuleSupportDimensionLE_restrict U V hU F r hF) := sorry

/-- The fibrewise support-dimension bound is preserved by flat pullback of
relative dimension `e`, with the bound shifted by `e`. -/
theorem fiberModuleSupportDimensionLE_flatPullback
    {X' X S : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (h : X' ⟶ X)
    (hf : h ≫ f = f') (e : ℕ) [Flat h] [RelativeDimension h e]
    (F : X.Modules) (r : ℕ) (hF : f.fiberModuleSupportDimensionLE F r) :
    f'.fiberModuleSupportDimensionLE ((Modules.pullback h).obj F) (r + e) := sorry

/-- Lemma 62.5.3 (3): the associated fibrewise cycle family of a quasi-coherent
finite-type module commutes with flat pullback of relative dimension `e`. -/
@[stacks 0H4R]
theorem moduleFiberCycleFamily_flatPullback
    {X' X S : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (h : X' ⟶ X)
    (hf : h ≫ f = f') (e : ℕ) [Flat h] [RelativeDimension h e]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (r : ℕ)
    (hF : f.fiberModuleSupportDimensionLE F r) :
    FiberCycleFamily.flatPullback h hf e (moduleFiberCycleFamily f F r hF) =
      FiberCycleFamily.reindex (Int.natCast_add r e)
        (moduleFiberCycleFamily f' ((Modules.pullback h).obj F) (r + e)
          (fiberModuleSupportDimensionLE_flatPullback h hf e F r hF)) := sorry

end AlgebraicGeometry.Scheme.Hom
