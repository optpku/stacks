/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.DerivedCoextension

variable {A B : Type u} [CommRing A] [CommRing B]
  [IsNoetherianRing A] [IsNoetherianRing B]

/-- Derived coextension along a finite map preserves bounded-below complexes with
finite cohomology modules. -/
theorem mapsBoundedBelowFiniteCohomology
    (f : A →+* B) (hf : f.Finite)
    (K : DerivedCategory (ModuleCat.{u, u} A))
    (hK_boundedBelow : ∃ n : ℤ, K.IsGE n)
    (hK_finite : ∀ i : ℤ,
      Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u, u} A) i).obj K)) :
    (∃ n : ℤ, ((derivedCoextensionOfScalars f).obj K).IsGE n) ∧
      ∀ i : ℤ, Module.Finite B
        ((DerivedCategory.homologyFunctor (ModuleCat.{u, u} B) i).obj
          ((derivedCoextensionOfScalars f).obj K)) := sorry

end CategoryTheory.ModuleCat.DerivedCoextension
