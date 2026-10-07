module

import StacksCheckRecall
public import stacks_project.Chap73.Lemma_73_9_3_FpqcCovering
public import stacks_project.Chap73.Lemma_73_9_3_Stability

open CategoryTheory

universe u v w

/- Lemma 73.9.3 (1): an isomorphism gives a singleton fpqc covering. -/
@[stacks 03MR]
#check (AlgebraicGeometry.AlgebraicSpace.fpqcCovering_singleton_of_isIso :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X X' : AlgebraicGeometry.AlgebraicSpace S}
    (f : X' ⟶ X) [IsIso f],
    AlgebraicGeometry.AlgebraicSpace.FpqcCovering
      (fun _ : Unit ↦ CategoryTheory.Over.mk f))

/- Lemma 73.9.3 (2): indexed composition preserves fpqc coverings. -/
@[stacks 03MR]
#check (AlgebraicGeometry.AlgebraicSpace.fpqcCovering_comp :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    {ι : Type v} {κ : ι → Type w}
    (family : ι → CategoryTheory.Over X)
    (refinement : (i : ι) → κ i → CategoryTheory.Over (family i).left),
    AlgebraicGeometry.AlgebraicSpace.FpqcCovering family →
      (∀ i : ι, AlgebraicGeometry.AlgebraicSpace.FpqcCovering (refinement i)) →
        AlgebraicGeometry.AlgebraicSpace.FpqcCovering (fun p : Sigma κ ↦
          CategoryTheory.Over.mk ((refinement p.1 p.2).hom ≫ (family p.1).hom)))

/- Lemma 73.9.3 (3): pullback preserves fpqc coverings. -/
@[stacks 03MR]
#check (AlgebraicGeometry.AlgebraicSpace.fpqcCovering_pullback :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X X' : AlgebraicGeometry.AlgebraicSpace S}
    {ι : Type v} (family : ι → CategoryTheory.Over X),
    AlgebraicGeometry.AlgebraicSpace.FpqcCovering family →
      ∀ (f : X' ⟶ X),
        AlgebraicGeometry.AlgebraicSpace.FpqcCovering (fun i : ι ↦
          (AlgebraicGeometry.AlgebraicSpace.overPullback f).obj (family i)))
