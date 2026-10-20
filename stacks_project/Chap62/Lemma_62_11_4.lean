module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.AssociatedCycle
import StacksCheckRecall

/-!
# Associated cycles of a cap product

This file records that the fibre-cycle action of the associated cycle family
of a coherent module flat over the base recovers the associated cycle of the
tensor with the pullback of a coherent module of bounded support dimension.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace CyclesOnFibers

/- Lemma 62.11.4: Let `(S, δ)` and `f : X ⟶ Y` be as in the fibre-cycle action
setup, and let `F` be a coherent `O_X`-module with `dim(Supp(F_y)) ≤ r` for all
`y ∈ Y`. Let `G` be a coherent `O_Y`-module with `dim_δ(Supp(G)) ≤ e`. Set
`α = [F/X/Y]_r` as `moduleFiberCycleFamily f F r hF` and `β = [G]_e` as
`Modules.relativeAssociatedCycle p δ G e`. If `F` is flat over `Y`, then
`α ∩ β = [F ⊗ (Modules.pullback f).obj G]_{r + e}`. -/
@[stacks 0H69] #check
  (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.cap_moduleFiberCycleFamily :
    ∀ {S X Y : Scheme.{u}} [UniversallyCatenary S]
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
          (RingedSpace.stalkModuleCat F x))),
    cap p f δ (moduleFiberCycleFamily f F r hF)
        (Modules.relativeAssociatedCycle p δ G e) =
      Modules.relativeAssociatedCycle (f ≫ p) δ
        (F ⊗ (Modules.pullback f).obj G) ((r : ℤ) + e))

/- The coefficientwise consequence of the same tensor-cycle equality. -/
#check
  (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.cap_moduleFiberCycleFamily_apply :
    ∀ {S X Y : Scheme.{u}}
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
          (RingedSpace.stalkModuleCat F x))) (x : X),
    CycleGroup.toAlgebraicCycle ((f ≫ p).relativeDimensionFunction δ)
        ((r : ℤ) + e)
        (cap p f δ (moduleFiberCycleFamily f F r hF)
          (Modules.relativeAssociatedCycle p δ G e)) x =
      CycleGroup.toAlgebraicCycle ((f ≫ p).relativeDimensionFunction δ)
        ((r : ℤ) + e)
        (Modules.relativeAssociatedCycle (f ≫ p) δ
          (F ⊗ (Modules.pullback f).obj G) ((r : ℤ) + e)) x)

end CyclesOnFibers
end AlgebraicGeometry.Scheme.Hom
