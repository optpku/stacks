/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Definition_66_29_1_RingedSite

/-!
# Filtered colimits of finitely presented modules on QCQS algebraic spaces

If `X` is a quasi-compact quasi-separated algebraic space over a scheme `S`,
every quasi-coherent `𝒪_X`-module is a small filtered colimit of finitely
presented modules.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- If `X` is a quasi-compact and quasi-separated algebraic space over a scheme `S`, then every
quasi-coherent `𝒪_X`-module is a small filtered colimit of finitely presented `𝒪_X`-modules. -/
theorem isFinitePresentation_ind {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X] (F : X.Modules) [F.IsQuasicoherent] :
    (SheafOfModules.isFinitePresentation (structureSheaf X)).ind.{u} F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
