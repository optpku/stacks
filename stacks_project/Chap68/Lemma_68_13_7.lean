/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap68.Lemma_68_4_3_Fibre
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap68.Lemma_68_13_12_ResidualSpace

/-!
# Residual spaces isomorphic to spectra of fields

A residual space of an algebraic space at a point is isomorphic to the spectrum
of a field if and only if the point is represented by a monomorphism from such
a spectrum. On a decent algebraic space this holds at every point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsResidualSpace

/-- Lemma 68.13.7 (1): Let `S` be a scheme. Let `X` be an algebraic space over
`S`. Let `x ∈ |X|`. The residual space of `X` at `x` is isomorphic to the
spectrum of a field if and only if `x` can be represented by a monomorphism
`Spec(k) ⟶ X` where `k` is a field. -/
@[stacks 0H1R]
theorem exists_iso_spec_iff_existsMonoFieldValuedPoint {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} {x : Points X} (ι : Z ⟶ X) [IsResidualSpace ι x] :
    (∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S),
        Nonempty (Z ≅ ofOver (Over.mk σ))) ↔
      existsMonoFieldValuedPoint X x :=
  sorry

/-- If a residual space is isomorphic to the spectrum of a field, then the marked
point is represented by a monomorphism from such a spectrum. -/
theorem existsMonoFieldValuedPoint_of_exists_iso_spec {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} {x : Points X} (ι : Z ⟶ X) [IsResidualSpace ι x]
    (hiso : ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S),
      Nonempty (Z ≅ ofOver (Over.mk σ))) :
    existsMonoFieldValuedPoint X x :=
  sorry

/-- If a point is represented by a monomorphism from the spectrum of a field,
then any residual space at that point is isomorphic to the spectrum of a
field. -/
theorem exists_iso_spec_of_existsMonoFieldValuedPoint {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} {x : Points X} (ι : Z ⟶ X) [IsResidualSpace ι x]
    (hx : existsMonoFieldValuedPoint X x) :
    ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S),
      Nonempty (Z ≅ ofOver (Over.mk σ)) :=
  sorry

/-- Lemma 68.13.7 (2): If `X` is a decent algebraic space over `S`, then every
residual space of `X` is isomorphic to the spectrum of a field. -/
@[stacks 0H1R]
theorem exists_iso_spec_of_isDecent {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    [IsDecent X] {x : Points X} (ι : Z ⟶ X) [IsResidualSpace ι x] :
    ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S),
      Nonempty (Z ≅ ofOver (Over.mk σ)) :=
  sorry

end IsResidualSpace

end AlgebraicGeometry.AlgebraicSpace
