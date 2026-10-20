/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.LinearProjection.GeneralPosition
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/- Lemma 43.23.3: if `Z` is a strict closed subvariety of a strict closed subvariety
`X` of `ℙ(V)` and `x : Z` is nonsingular on `X`, then there is a nonempty Zariski-open
locus of closed projection centers such that the projection of `Z` is an isomorphism onto
its scheme-theoretic image over an open neighborhood of the image of `x`. -/
@[stacks 0H8A] #check
  (AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearProjection.exists_open_isIso_toImage_restrict_near_of_strictSubvariety :
    ∀ (Z X : SchemeOverField k) [Variety Z] [Variety X]
      (j : Z ⟶ X) (i : X ⟶ Over.mk (ProjectiveSpace.VectorSpace.toSpec k V))
      [IsClosedImmersion j.left] [IsClosedImmersion i.left]
      (hZX : Set.range j.left.base ≠ Set.univ)
      (hXP : Set.range i.left.base ≠ Set.univ)
      (x : Z.left), X.hom.SmoothAt (j.left.base x) →
        ∀ (projection : ∀ (p : ProjectiveSpace.VectorSpace.scheme k V),
          IsClosed ({p} : Set (ProjectiveSpace.VectorSpace.scheme k V)) →
            ProjectiveSpace.VectorSpace.LinearProjection k V p),
          ∃ U : (ProjectiveSpace.VectorSpace.scheme k V).Opens, Nonempty U ∧
            ∀ (p : ProjectiveSpace.VectorSpace.scheme k V), p ∈ U →
              (hp : IsClosed ({p} : Set (ProjectiveSpace.VectorSpace.scheme k V))) →
                p ∉ Set.range (j ≫ i).left.base ∧
                  ∀ hpi : p ∉ Set.range (j ≫ i).left.base,
                    let f := (projection p hp).restrict (j ≫ i).left
                      ((projection p hp).range_subset_domain (j ≫ i).left hpi)
                    ∃ R : f.image.Opens, f.toImage x ∈ R ∧ IsIso (f.toImage ∣_ R))
