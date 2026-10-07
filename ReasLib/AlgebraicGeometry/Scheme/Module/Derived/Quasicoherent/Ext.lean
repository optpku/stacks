module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.CategoryTheory.DerivedCategory.Ext

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- For a bounded complex with quasi-coherent cohomology on a quasi-compact and
quasi-separated scheme, Ext from any finite locally free module vanishes in all sufficiently
large degrees. -/
theorem extSubsingletonEventually {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (E : Bounded X) :
    ∃ n₀ : ℤ, 0 < n₀ ∧
      ∀ (F : X.Modules) [F.IsFiniteLocallyFree] (n : ℤ), n₀ ≤ n →
        Subsingleton
          (Ext⁽n⁾((DerivedCategory.singleFunctor X.toRingedSpace.Modules 0).obj F,
            DerivedCategory.Bounded.ι.obj E.obj)) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
