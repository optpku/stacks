/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Cech
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Module-valued Cech complexes for presheaves on a ringed space

This leaf specializes the generic ringed-site Cech construction to the opens site of a ringed
space while retaining presheaf modules as the coefficient domain.  The sheaf-valued
`ModuleCech.Sections` owner is a separate specialization; keeping the two domains distinct avoids
silently replacing the source presheaf statement by a sheaf statement.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleCech.Presheaf

variable {X : RingedSpace.{u}} (U : Opens X.carrier)
variable {ι : Type u} (family : ι → Over U)

/- The presheaf of `𝒪_X(U)`-modules obtained by restricting a presheaf module to `Over U`. -/
@[stacks 01EI "20.10.0.1: presheaf-module sections on a ringed space"]
abbrev sections :
    X.PresheafModules ⥤
      (Over U)ᵒᵖ ⥤ ModuleCat (sectionsRingOnOpen X U) :=
  SheafOfModules.RingedSite.sectionsOnOver X.ringCatSheaf U

/-- The module-valued Čech cochain-complex functor for a family in `Over U`. -/
@[stacks 01EI "20.10.0.1: presheaf-module Cech complex on a ringed space"]
abbrev complex :
    X.PresheafModules ⥤ CochainComplex (ModuleCat (sectionsRingOnOpen X U)) ℕ :=
  SheafOfModules.RingedSite.cechComplex X.ringCatSheaf U family

/-- The presheaf-module Cech complex inherits zero-morphism preservation from the ringed-site
complex owner. -/
instance complex_preservesZeroMorphisms :
    (complex U family).PreservesZeroMorphisms := sorry

/- The degree-`p` module-valued Čech cohomology of a presheaf module. -/
@[stacks 01EI "20.10.0.1: presheaf-module Cech cohomology on a ringed space"]
abbrev cohomology (M : X.PresheafModules) (p : ℕ) :
    ModuleCat (sectionsRingOnOpen X U) :=
  SheafOfModules.RingedSite.cechCohomology X.ringCatSheaf U family M p



end AlgebraicGeometry.RingedSpace.ModuleCech.Presheaf

end
