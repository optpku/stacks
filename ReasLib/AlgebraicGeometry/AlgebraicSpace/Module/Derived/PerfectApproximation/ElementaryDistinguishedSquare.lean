/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PerfectApproximation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ElementaryDistinguishedSquare
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Restriction

/-! # Perfect approximation along an elementary distinguished square -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.HasPerfectApproximation

/-- In an elementary distinguished square, perfect approximation on the étale
member implies perfect approximation on the whole space when the closed support
lies outside the open member and all cohomology sheaves in degrees at least `m`
are supported on that closed subset. -/
theorem of_isElementaryDistinguishedSquare
    {S : Scheme.{u}} {U V X : AlgebraicSpace S} (j : U ⟶ X) (f : V ⟶ X)
    [Etale f] [IsElementaryDistinguishedSquare j f] (T : Closeds (Points X))
    (hT : (T : Set (Points X)) ⊆ (toOpenSubspace j f).pointsSetᶜ) (E : DerivedQCoh X)
    (m : ℤ)
    (hV : HasPerfectApproximation (T.preimage (Points.continuous_map f))
      (DerivedQCoh.restrict f E) m)
    (hE : ∀ i : ℤ, m ≤ i →
      Modules.moduleSupportedOn (T : Set (Points X))
        ((DerivedCategory.homologyFunctor (Modules X) i).obj E.obj)) :
    HasPerfectApproximation T E m :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.HasPerfectApproximation
