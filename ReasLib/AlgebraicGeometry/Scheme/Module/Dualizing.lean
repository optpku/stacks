/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay.Locality
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Locality
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- A coherent module on a locally Noetherian scheme is dualizing when every shift of
its degree-zero derived complex is an intrinsic dualizing complex. -/
def IsDualizingModule {X : Scheme.{u}} [IsLocallyNoetherian X]
    (ω : X.Modules) : Prop :=
  ω.IsCoherent ∧ ∀ n : ℤ,
    IsDualizingComplex (((DerivedCategory.singleFunctor X.Modules 0).obj ω)⟦n⟧)

/-- The coherence-and-all-shifts characterization of a dualizing module. -/
theorem isDualizingModule_iff {X : Scheme.{u}} [IsLocallyNoetherian X]
    (ω : X.Modules) :
    IsDualizingModule ω ↔
      ω.IsCoherent ∧ ∀ n : ℤ,
        IsDualizingComplex (((DerivedCategory.singleFunctor X.Modules 0).obj ω)⟦n⟧) := sorry

namespace IsDualizingModule

/-- Every integer shift of the degree-zero complex of a dualizing module is dualizing. -/
theorem shift {X : Scheme.{u}} [IsLocallyNoetherian X] {ω : X.Modules}
    (hω : IsDualizingModule ω) (n : ℤ) :
    IsDualizingComplex (((DerivedCategory.singleFunctor X.Modules 0).obj ω)⟦n⟧) := sorry

/-- On a connected locally Noetherian Cohen–Macaulay scheme, existence of a dualizing
module is equivalent to existence of an intrinsic dualizing complex. -/
theorem exists_iff_existsComplex_of_connected
    (X : Scheme.{u}) [IsLocallyNoetherian X] [ConnectedSpace X]
    [CohenMacaulay X] :
    (∃ ω : X.Modules, IsDualizingModule ω) ↔
      ∃ K : RingedSpace.ModuleDerived X.toRingedSpace, IsDualizingComplex K := sorry

end IsDualizingModule
end AlgebraicGeometry.Scheme
