/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.VectorBundleLocus

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.IsPerfect

/- Lemma 36.31.3: the canonical open `vectorBundleLocus hE i r` is the locus on which `E`
is a finite locally free module of rank `r` placed in degree `i`; a scheme morphism factors
through this open exactly when its derived pullback has the same property. -/
@[stacks 0BDK] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.IsPerfect.vectorBundleLocus_spec :
    ∀ {X : Scheme.{u}} {E : RingedSpace.ModuleDerived X.toRingedSpace}
      (hE : RingedSpace.ModuleDerived.IsPerfect E) (i r : ℤ),
    IsVectorBundleOfRankInDegree
        ((RingedSpace.modulePullbackDerived (vectorBundleLocus hE i r).ι.toShHom).obj E) i r ∧
      ∀ {Y : Scheme.{u}} (f : Y ⟶ X),
        (∃ g : Y ⟶ (vectorBundleLocus hE i r).toScheme,
          g ≫ (vectorBundleLocus hE i r).ι = f) ↔
        IsVectorBundleOfRankInDegree
          ((RingedSpace.modulePullbackDerived f.toShHom).obj E) i r)

end AlgebraicGeometry.Scheme.ModuleDerived.IsPerfect
