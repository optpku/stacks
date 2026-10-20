module

public import Mathlib.Data.List.TFAE
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.DualizingModule
public import ReasLib.CategoryTheory.DerivedCategory.Concentrated.Basic
public import ReasLib.RingTheory.CohenMacaulay.Maximal

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]

/-- For a normalized dualizing complex over a Noetherian local ring, Cohen--Macaulayness
of the ring, concentration in one degree, and the dimension-shift description of the
complex are equivalent. -/
theorem cohenMacaulay_tfae
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : ω.IsNormalizedDualizingComplex H) :
    let d := ((ringKrullDim A).unbotD 0).toNat
    List.TFAE
      [ Module.CohenMacaulay A A
      , ∃ i : ℤ, DerivedCategory.concentrated (ModuleCat.{u} A) i ω
      , Nonempty
          (ω ≅ ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (dualizingModule H ω hω))⟦(d : ℤ)⟧)
      ] := sorry

/-- Over a Cohen--Macaulay Noetherian local ring, the dualizing module of a normalized
dualizing complex is maximal Cohen--Macaulay. -/
theorem dualizingModuleMaximalCohenMacaulay
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : ω.IsNormalizedDualizingComplex H)
    [Module.CohenMacaulay A A] :
    Module.MaximalCohenMacaulay A (dualizingModule H ω hω) := sorry

end CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

end
