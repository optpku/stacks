/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.KrullDimension.Module
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]

/-- The dualizing module associated to a normalized dualizing complex is its cohomology
in degree minus the Krull dimension of the ring. -/
noncomputable def dualizingModule
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : ω.IsNormalizedDualizingComplex H) : ModuleCat.{u} A :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A)
    (-(((ringKrullDim A).unbotD 0).toNat : ℤ))).obj ω

/-- If the Krull dimension is the natural number `d`, the dualizing module is the
degree-`-d` cohomology module. -/
theorem dualizingModule_eq_of_krullDim
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : ω.IsNormalizedDualizingComplex H)
    (d : ℕ) (hd : ringKrullDim A = d) :
    dualizingModule H ω hω =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj ω := sorry

end CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

end
