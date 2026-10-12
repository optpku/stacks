/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.SectionRingProj
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Situation 28.28.1: for an ample invertible module `L` on a scheme `X`, the projective
spectrum of its tensor-power section ring admits the canonical morphism from `X`, together with
the canonical graded comparison from pulled-back projective twists to the integral powers of
`L`. -/
@[stacks 01QH] #check
  (AlgebraicGeometry.Scheme.Modules.IsAmple.exists_sectionRingProj :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} {L : X.Modules}
      [AlgebraicGeometry.Scheme.Modules.Invertible L],
      AlgebraicGeometry.Scheme.Modules.IsAmple L →
        ∃ f : X ⟶ AlgebraicGeometry.Proj
            (AlgebraicGeometry.RingedSpace.GradedSections.grading L),
          AlgebraicGeometry.Scheme.Modules.IsSectionRingProjMap L f)
