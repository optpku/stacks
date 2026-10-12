/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.DerivedAdeq.Comparison

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/-! Compatibility checks for the derived adequacy comparison API. -/

#check (SheafOfModules.derivedAdequateProperty :
  ∀ (S : Scheme.{u}) (τ : StandardTopology),
    ObjectProperty
      (RingedSite.Hom.ModuleDerived.{u + 1}
        (StandardTopology.Big.ringedSite τ S)))

#check (SheafOfModules.DerivedAdeq.toFppf_isEquivalence :
  ∀ (S : Scheme.{u}) (τ : StandardTopology),
    Functor.IsEquivalence (SheafOfModules.DerivedAdeq.toFppf S τ))

end
