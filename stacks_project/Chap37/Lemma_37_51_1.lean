/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.ProjComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.SectionRingProj.RatioOpen
public import stacks_project.Chap37.«37_51_0_1_ProjSpec»
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.CanonicalRelativeProjComparison
open AlgebraicGeometry.ProjSpec
open AlgebraicGeometry.Scheme.Modules.IsSectionRingProjMap
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.51.1: if `P` is proper over `R` and `L` is an ample invertible
`P.Modules` object, then the canonical comparison from `P` to the relative projective
spectrum of its nonnegative tensor-power section algebra is an isomorphism. -/
@[stacks 0EKI] #check
  (AlgebraicGeometry.CanonicalRelativeProjComparison.exists_isIso_of_isProperOverSpec :
    ∀ {R : Type u} [CommRing R] {P : Scheme.{u}}
      (p : P ⟶ Spec (CommRingCat.of R)) [IsProper p]
      (L : P.Modules) [Scheme.Modules.Invertible L] [Scheme.Modules.IsAmple L],
      ∃ C : AlgebraicGeometry.CanonicalRelativeProjComparison p L, IsIso C.comparison)

/- For every `n : ℤ`, the canonical comparison identifies the projective twist `𝒪(n)`
with the tensor power `L ^⊗ n`. -/
#check
  (AlgebraicGeometry.Scheme.Modules.IsSectionRingProjMap.comparison_component_isIso :
    ∀ {X : Scheme.{u}} {L : X.Modules}
      [Scheme.Modules.Invertible L] [Scheme.Modules.IsAmple L]
      {f : X ⟶ Proj (RingedSpace.GradedSections.grading L)},
      Scheme.Modules.IsSectionRingProjMap L f →
        ∀ (P : ProjTwistPresentation (RingedSpace.GradedSections.grading L))
          (c : Scheme.Modules.SectionRingProjComparison L P f),
          c.IsCanonical → ∀ n : ℤ, IsIso (c.component n))

/- The integral and nonnegative tensor-power relative spectra fit into the canonical
two-square Proj–Spec diagram. -/
#check
  (AlgebraicGeometry.ProjSpec.diagram :
    (C : AlgebraicGeometry.ProjSpec.Construction) → AlgebraicGeometry.ProjSpec.Diagram C)
