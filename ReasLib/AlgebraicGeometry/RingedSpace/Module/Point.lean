/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Indiscrete
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Point
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Module sheaves on a ringed point

Modules over a commutative ring are canonically equivalent to module sheaves on the associated
ringed point. The construction is the composite of scalar transport to the top-open ring and the
generic equivalence between modules on the top open and module sheaves on a nonempty indiscrete
space.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedPoint.Module

variable (R : Type u) [CommRing R]

/-- Restriction of scalars along `RingedPoint.topRingIso R` identifies `R`-modules with modules
over the top-open value of the ringed-point structure sheaf. -/
noncomputable def topEquivalence :
    ModuleCat.{u} R ≌
      ModuleCat.{u} ((RingedPoint.ringCatSheaf R).obj.obj
        (op (⊤ : Opens RingedPoint.carrier))) :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (RingedPoint.topRingIso R).ringCatIsoToRingEquiv

/-- `R`-modules are canonically equivalent to module sheaves on `RingedPoint.of R`. -/
@[stacks 01BH "modules on a ringed point"]
noncomputable def equivalence : ModuleCat.{u} R ≌ (RingedPoint.of R).Modules :=
  (topEquivalence R).trans
    (SheafOfModules.Indiscrete.equivalence (RingedPoint.ringCatSheaf R))

/-- An `R`-module determines functorially its canonical module sheaf on `RingedPoint.of R`. -/
@[stacks 01BH "modules as module sheaves on a ringed point"]
noncomputable abbrev functor : ModuleCat.{u} R ⥤ (RingedPoint.of R).Modules :=
  (equivalence R).functor

/-- Evaluation on the top open, transported back to `R`, is the inverse point-module functor. -/
noncomputable abbrev topSectionsFunctor :
    (RingedPoint.of R).Modules ⥤ ModuleCat.{u} R :=
  (equivalence R).inverse

/-- The module sheaf on `RingedPoint.of R` corresponding to an `R`-module. -/
@[stacks 01BH "module sheaf on a ringed point"]
noncomputable abbrev sheaf (M : ModuleCat.{u} R) : (RingedPoint.of R).Modules :=
  (functor R).obj M

/-- The top-open value of `sheaf R M` is the scalar transport of `M` along
`RingedPoint.topRingIso R`. -/
noncomputable def topValueIso (M : ModuleCat.{u} R) :
    (sheaf R M).val.obj (op (⊤ : Opens RingedPoint.carrier)) ≅
      (topEquivalence R).functor.obj M :=
  SheafOfModules.Indiscrete.topValueIso
    (R := RingedPoint.ringCatSheaf R) ((topEquivalence R).functor.obj M)

/-- Forming the module sheaf on a ringed point is an equivalence of categories. -/
noncomputable instance functor_isEquivalence : (functor R).IsEquivalence := sorry

end AlgebraicGeometry.RingedPoint.Module
