/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.Algebra.Module.DifferentialOperator.Derivation

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A derivation of an affine base ring induces a module derivation on the
cohomology of every quasi-compact, quasi-separated, étale morphism to that
affine scheme. -/
theorem existsCohomologyDerivationOperator
    {A : Type u} [CommRing A] {V : Scheme.{u}}
    (f : V ⟶ Spec (CommRingCat.of A))
    [QuasiCompact f] [QuasiSeparated f] [Etale f]
    (θ : Derivation ℤ A A) (i : ℕ) :
    ∃ D : Module.End ℤ
        (cohomology f (SheafOfModules.unit V.ringCatSheaf : V.Modules) i),
      D.IsModuleDerivation θ := sorry

end AlgebraicGeometry.Scheme.Hom
