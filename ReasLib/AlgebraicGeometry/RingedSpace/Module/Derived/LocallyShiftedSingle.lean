/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.LocallyConstant.Clopen
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived

@[expose] public section

open CategoryTheory DerivedCategory

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}

/-- A derived module is locally a fixed module in the degree prescribed by a locally
constant natural-valued function. -/
def IsLocallyShiftedSingle (E : ModuleDerived X) (ω : X.Modules)
    (d : LocallyConstant X ℕ) : Prop :=
  ∀ n : ℕ, IsIsomorphic
    ((moduleRestrictionToOpenDerived X (d.fiberClopen n).toOpens).obj
      (((singleFunctor X.Modules 0).obj ω)⟦(n : ℤ)⟧))
    ((moduleRestrictionToOpenDerived X (d.fiberClopen n).toOpens).obj E)

/-- The locally shifted-single property is exactly the family of restricted
isomorphisms on the clopen degree loci. -/
theorem isLocallyShiftedSingle_iff (E : ModuleDerived X) (ω : X.Modules)
    (d : LocallyConstant X ℕ) :
    IsLocallyShiftedSingle E ω d ↔
      ∀ n : ℕ, IsIsomorphic
        ((moduleRestrictionToOpenDerived X (d.fiberClopen n).toOpens).obj
          (((singleFunctor X.Modules 0).obj ω)⟦(n : ℤ)⟧))
        ((moduleRestrictionToOpenDerived X (d.fiberClopen n).toOpens).obj E) := sorry

namespace IsLocallyShiftedSingle

/-- The locally shifted-single property is invariant under isomorphism of derived
modules. -/
theorem of_isIsomorphic {E E' : ModuleDerived X} {ω : X.Modules}
    {d : LocallyConstant X ℕ} (hE : IsLocallyShiftedSingle E ω d)
    (h : IsIsomorphic E E') : IsLocallyShiftedSingle E' ω d := sorry

end IsLocallyShiftedSingle
end AlgebraicGeometry.RingedSpace.ModuleDerived
