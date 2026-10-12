/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay.Locus
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.LocalConcentration
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Duality
public import ReasLib.AlgebraicGeometry.Scheme.Module.CohenMacaulay

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpace.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IsDualizingComplex

/-- A locally Noetherian scheme with a dualizing complex is Cohen-Macaulay exactly when the
complex is locally concentrated in one degree. -/
theorem cohenMacaulay_iff_isLocallyConcentrated
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ω : RingedSpace.ModuleDerived X.toRingedSpace} (hω : IsDualizingComplex ω) :
    Scheme.CohenMacaulay X ↔ RingedSpace.ModuleDerived.IsLocallyConcentrated ω := sorry

/-- The local ring at `x` is Cohen-Macaulay exactly when the derived stalk of a dualizing
complex at `x` is concentrated in one degree. -/
theorem stalk_cohenMacaulay_iff_concentrated
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ω : RingedSpace.ModuleDerived X.toRingedSpace} (hω : IsDualizingComplex ω) (x : X) :
    Module.CohenMacaulay (X.presheaf.stalk x) (X.presheaf.stalk x) ↔
      ∃ n : ℤ, DerivedCategory.concentrated (ModuleCat (X.presheaf.stalk x)) n
        (Stalk.obj ω x) := sorry

/-- The locus of points with Cohen-Macaulay local ring is open for a dualizing complex. -/
theorem isOpen_cohenMacaulayLocus
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ω : RingedSpace.ModuleDerived X.toRingedSpace} (hω : IsDualizingComplex ω) :
    IsOpen (Scheme.cohenMacaulayLocus X) := sorry

/-- The open subset cut out by the Cohen-Macaulay locus of a chosen dualizing complex. -/
def cohenMacaulayOpen
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ω : RingedSpace.ModuleDerived X.toRingedSpace} (hω : IsDualizingComplex ω) :
    X.Opens :=
  ⟨Scheme.cohenMacaulayLocus X, hω.isOpen_cohenMacaulayLocus⟩

/-- The carrier of `cohenMacaulayOpen` is the Cohen-Macaulay locus. -/
theorem coe_cohenMacaulayOpen
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ω : RingedSpace.ModuleDerived X.toRingedSpace} (hω : IsDualizingComplex ω) :
    (hω.cohenMacaulayOpen : Set X) = Scheme.cohenMacaulayLocus X := sorry

/-- The open subscheme on the Cohen-Macaulay locus is Cohen-Macaulay. -/
theorem cohenMacaulayOpen_isCohenMacaulay
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ω : RingedSpace.ModuleDerived X.toRingedSpace} (hω : IsDualizingComplex ω) :
    Scheme.CohenMacaulay hω.cohenMacaulayOpen.toScheme := sorry

/-- On a connected Cohen-Macaulay scheme, a dualizing complex is a shift of its coherent
Cohen-Macaulay cohomology sheaf in one degree. -/
theorem exists_canonicalModule_of_connected
    {X : Scheme.{u}} [IsLocallyNoetherian X] [ConnectedSpace X] [Scheme.CohenMacaulay X]
    {ω : RingedSpace.ModuleDerived X.toRingedSpace} (hω : IsDualizingComplex ω) :
    ∃ n : ℤ,
      let ωX := cohomologySheaf ω n
      ωX.IsCoherent ∧ LocallyRingedSpace.Modules.CohenMacaulay ωX ∧
        Nonempty (ω ≅ ((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦-n⟧) := sorry

end AlgebraicGeometry.Scheme.IsDualizingComplex
