/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.LinearProjection.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety

/-!
# General-position linear projections

This file records the local behavior at a smooth point of linear projections from general closed
centers in projective space.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearProjection

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- If a closed subvariety of `ℙ(V)` has dimension less than `n - 1`, then at a smooth point
its projection from every closed center in a nonempty open locus is locally an isomorphism onto
its scheme-theoretic image. -/
theorem exists_open_isIso_toImage_restrict_near
    (n : ℕ) (hV : Module.finrank k V = n + 1)
    (X : SchemeOverField k) [Variety X]
    (i : X ⟶ Over.mk (toSpec k V)) [IsClosedImmersion i.left]
    (x : X.left) (hx : X.hom.SmoothAt x)
    (hXdim : topologicalKrullDim X.left < (n - 1 : ℕ))
    (projection : ∀ (p : scheme k V),
      IsClosed ({p} : Set (scheme k V)) → LinearProjection k V p) :
    ∃ U : (scheme k V).Opens, Nonempty U ∧
      ∀ (p : scheme k V), p ∈ U →
        (hp : IsClosed ({p} : Set (scheme k V))) →
          p ∉ Set.range i.left.base ∧
            ∀ hpi : p ∉ Set.range i.left.base,
              let f := (projection p hp).restrict i.left
                ((projection p hp).range_subset_domain i.left hpi)
              ∃ R : f.image.Opens, f.toImage x ∈ R ∧ IsIso (f.toImage ∣_ R) := sorry

/-- If a closed subvariety of `ℙ(V)` has dimension `n - 1`, then at a smooth point its
projection from every closed center in a nonempty open locus is étale.

The dimension hypothesis is stated as `dim X + 1 = n`, matching the integer subtraction of the
source: for `n = 0` it is unsatisfiable, rather than truncating to `dim X = 0`. -/
theorem exists_open_etaleAt_restrict
    (n : ℕ) (hV : Module.finrank k V = n + 1)
    (X : SchemeOverField k) [Variety X]
    (i : X ⟶ Over.mk (toSpec k V)) [IsClosedImmersion i.left]
    (x : X.left) (hx : X.hom.SmoothAt x)
    (hXdim : topologicalKrullDim X.left + 1 = n)
    (projection : ∀ (p : scheme k V),
      IsClosed ({p} : Set (scheme k V)) → LinearProjection k V p) :
    ∃ U : (scheme k V).Opens, Nonempty U ∧
      ∀ (p : scheme k V), p ∈ U →
        (hp : IsClosed ({p} : Set (scheme k V))) →
          p ∉ Set.range i.left.base ∧
            ∀ hpi : p ∉ Set.range i.left.base,
              ((projection p hp).restrict i.left
                ((projection p hp).range_subset_domain i.left hpi)).EtaleAt x := sorry

/-- For strict nested closed subvarieties of projective space, a smooth point of the
larger subvariety has a neighborhood on which a general linear projection of the
smaller subvariety is an isomorphism onto its scheme-theoretic image. -/
theorem exists_open_isIso_toImage_restrict_near_of_strictSubvariety
    (Z X : SchemeOverField k) [Variety Z] [Variety X]
    (j : Z ⟶ X) (i : X ⟶ Over.mk (toSpec k V))
    [IsClosedImmersion j.left] [IsClosedImmersion i.left]
    (hZX : Set.range j.left.base ≠ Set.univ)
    (hXP : Set.range i.left.base ≠ Set.univ)
    (x : Z.left) (hx : X.hom.SmoothAt (j.left.base x))
    (projection : ∀ (p : scheme k V),
      IsClosed ({p} : Set (scheme k V)) → LinearProjection k V p) :
    ∃ U : (scheme k V).Opens, Nonempty U ∧
      ∀ (p : scheme k V), p ∈ U →
        (hp : IsClosed ({p} : Set (scheme k V))) →
          p ∉ Set.range (j ≫ i).left.base ∧
            ∀ hpi : p ∉ Set.range (j ≫ i).left.base,
              let f := (projection p hp).restrict (j ≫ i).left
                ((projection p hp).range_subset_domain (j ≫ i).left hpi)
              ∃ R : f.image.Opens, f.toImage x ∈ R ∧ IsIso (f.toImage ∣_ R) := sorry

end AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearProjection
