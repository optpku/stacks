module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.RegularVanishing
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 57.9.4 (1): on a regular Noetherian scheme of dimension `d`, every
degree-`n` extension class between coherent modules is zero when `d < n`. -/
@[stacks 0FZ3] #check
  (AlgebraicGeometry.Scheme.Modules.ext_eq_zero_of_gt_dimension :
    ∀ {X : Scheme.{u}} [IsNoetherian X] [Scheme.Regular X]
      (d : ℕ), topologicalKrullDim X = d →
      (F G : X.Modules) → [F.IsCoherent] → [G.IsCoherent] →
      (n : ℕ) → d < n →
      (e : @CategoryTheory.Abelian.Ext X.Modules inferInstance inferInstance
        (@CategoryTheory.IsGrothendieckAbelian.hasExt X.Modules inferInstance inferInstance
          (SheafOfModules.isGrothendieckAbelian X.ringCatSheaf)) F G n) →
      e = 0)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.ModuleDerived

/- Lemma 57.9.4 (2): on a regular Noetherian scheme of dimension `d`, every
morphism `K ⟶ L` between bounded coherent complexes is zero when the cohomology of
`K` vanishes below `a + d` and the cohomology of `L` vanishes from `a` onward. -/
@[stacks 0FZ3] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.hom_eq_zero_of_cohomology_gap :
    ∀ {X : Scheme.{u}} [IsNoetherian X] [Scheme.Regular X]
      (d : ℕ), topologicalKrullDim X = d →
      (K L : Dᵇ[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf]) →
      (a : ℤ) →
      (∀ i : ℤ, i < a + (d : ℤ) →
        IsZero ((DerivedCategory.Bounded.homologyFunctor X.Modules i).obj K.obj)) →
      (∀ i : ℤ, a ≤ i →
        IsZero ((DerivedCategory.Bounded.homologyFunctor X.Modules i).obj L.obj)) →
      (f : K ⟶ L) → f = 0)

end AlgebraicGeometry.Scheme.ModuleDerived
