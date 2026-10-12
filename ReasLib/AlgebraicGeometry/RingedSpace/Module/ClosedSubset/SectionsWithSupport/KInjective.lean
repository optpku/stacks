/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Adjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.SectionsWithSupport
import Mathlib.Tactic.CrossRefAttribute

/-!
# K-injective complexes and sections with support

The sections-with-support functor is right adjoint to exact closed-subset pushforward, so its
termwise action preserves K-injective cochain complexes.  The bundled closed subset is the only
geometric support parameter.
-/

@[expose] public section

open CategoryTheory ComplexShape TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ClosedSubset.SectionsWithSupport

variable (X : RingedSpace.{u}) (Z : Closeds X)

/-- The termwise sections-with-support image of an ambient cochain complex. -/
@[stacks 0G6Z "sections with support on cochain complexes"]
abbrev mapComplex (I : CochainComplex X.Modules ℤ) :
    CochainComplex (RingedSpace.ClosedSubset.Modules X Z) ℤ :=
  ((functor X Z).mapHomologicalComplex (up ℤ)).obj I

/-- Sections with support in a bundled closed subset preserve K-injective cochain complexes. -/
@[stacks 0G6Z "sections with support preserve K-injective complexes"]
instance mapIsKInjective
    (I : CochainComplex X.Modules ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective (mapComplex X Z I) := sorry

end AlgebraicGeometry.RingedSpace.ClosedSubset.SectionsWithSupport
