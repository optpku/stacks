/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.SectionRingProj.OpenImmersion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 28.26.11: for an ample invertible module `L` on a scheme `X`, a morphism
`f : X ⟶ Proj (RingedSpace.GradedSections.grading L)` with the canonical section-ring
projective properties is an open immersion with dense image. -/
@[stacks 01Q1]
#check (AlgebraicGeometry.Scheme.Modules.IsSectionRingProjMap.isOpenImmersion_and_isDominant :
  ∀ {X : Scheme.{u}} {L : X.Modules}
    [AlgebraicGeometry.Scheme.Modules.Invertible L]
    [AlgebraicGeometry.Scheme.Modules.IsAmple L]
    {f : X ⟶ Proj (RingedSpace.GradedSections.grading L)},
    AlgebraicGeometry.Scheme.Modules.IsSectionRingProjMap L f →
      IsOpenImmersion f ∧ IsDominant f)
