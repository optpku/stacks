/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap20.Lemma_20_50_5
public import stacks_project.Chap36.Lemma_36_13_4
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.CohomologyDetection
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 36.13.5 (1): for a perfect object on a quasi-compact quasi-separated scheme,
there is a finite cohomological window whose vanishing detects vanishing of morphisms
from that object to any object of `D_QCoh(𝒪_X)`. -/
@[stacks 09M4] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.exists_homologyWindow_of_isPerfect :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      {K : RingedSpace.ModuleDerived X.toRingedSpace},
      RingedSpace.ModuleDerived.IsPerfect K →
        ∃ a b : ℤ, a ≤ b ∧
          ∀ L : DerivedQCoh X,
            (∀ i ∈ Set.Icc a b,
              IsZero ((DerivedCategory.homologyFunctor X.toRingedSpace.Modules i).obj
                ((inclusion X).obj L))) →
              Subsingleton (K ⟶ (inclusion X).obj L))

/- Lemma 36.13.5 (2): derived Ext from a perfect object to a bounded object of
`D_QCoh(𝒪_X)` vanishes outside a finite interval of integer degrees. -/
@[stacks 09M4] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.exists_extSupportInterval_of_isPerfect :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      {K : RingedSpace.ModuleDerived X.toRingedSpace},
      RingedSpace.ModuleDerived.IsPerfect K →
        ∀ L : Bounded X,
          ∃ c d : ℤ, c ≤ d ∧
            ∀ n : ℤ, n ∉ Set.Icc c d →
              Subsingleton (Ext⁽n⁾(K, DerivedCategory.Bounded.ι.obj L.obj)))

end AlgebraicGeometry.Scheme.DerivedQCoh
