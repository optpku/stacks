module

public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Cap
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle.FiberFamily
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Coherent

/-!
# Associated cycles and fibre-cycle actions

The fibre-cycle action of the associated cycle family of a relatively flat
coherent module agrees with the associated cycle of its tensor product with a
pulled-back coherent module.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace CyclesOnFibers

/-- The fibre-cycle action of a relatively flat coherent module agrees with the
associated cycle of its tensor product with a pulled-back coherent module. -/
theorem cap_moduleFiberCycleFamily {S X Y : Scheme.{u}} [UniversallyCatenary S]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] [LocallyOfFiniteType (f ≫ p)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (F : X.Modules) [F.IsCoherent] (r : ℕ)
    (hF : f.fiberModuleSupportDimensionLE F r)
    (G : Y.Modules) [G.IsCoherent] (e : ℤ)
    (hG : ∀ y ∈ Modules.moduleSupport G, p.relativeDimensionFunction δ y ≤ e)
    (hflat : ∀ x : X,
      Module.Flat (Y.presheaf.stalk (f x))
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
          (RingedSpace.stalkModuleCat F x))) :
    cap p f δ (moduleFiberCycleFamily f F r hF)
        (Modules.relativeAssociatedCycle p δ G e) =
      Modules.relativeAssociatedCycle (f ≫ p) δ
        (F ⊗ (Modules.pullback f).obj G) ((r : ℤ) + e) := sorry

/-- Evaluating the fibre-cycle action compares the coefficients of the action
with those of the associated cycle of the corresponding tensor product. -/
theorem cap_moduleFiberCycleFamily_apply {S X Y : Scheme.{u}}
    [UniversallyCatenary S] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] [LocallyOfFiniteType (f ≫ p)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (F : X.Modules) [F.IsCoherent] (r : ℕ)
    (hF : f.fiberModuleSupportDimensionLE F r)
    (G : Y.Modules) [G.IsCoherent] (e : ℤ)
    (hG : ∀ y ∈ Modules.moduleSupport G, p.relativeDimensionFunction δ y ≤ e)
    (hflat : ∀ x : X,
      Module.Flat (Y.presheaf.stalk (f x))
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
          (RingedSpace.stalkModuleCat F x))) (x : X) :
    CycleGroup.toAlgebraicCycle ((f ≫ p).relativeDimensionFunction δ)
        ((r : ℤ) + e)
        (cap p f δ (moduleFiberCycleFamily f F r hF)
          (Modules.relativeAssociatedCycle p δ G e)) x =
      CycleGroup.toAlgebraicCycle ((f ≫ p).relativeDimensionFunction δ)
        ((r : ℤ) + e)
        (Modules.relativeAssociatedCycle (f ≫ p) δ
          (F ⊗ (Modules.pullback f).obj G) ((r : ℤ) + e)) x := sorry

end CyclesOnFibers
end AlgebraicGeometry.Scheme.Hom
