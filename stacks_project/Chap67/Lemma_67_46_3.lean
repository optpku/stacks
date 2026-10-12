/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap67.Lemma_67_46_3_FiniteLocallyFree

/-!
# Characterizations of finite locally free morphisms of algebraic spaces

Lemma 67.46.3 records that a morphism of algebraic spaces is finite locally
free iff it is representable and finite locally free, iff some surjective étale
scheme atlas has finite locally free projection, and iff some Zariski covering
of the target has finite locally free inverse images.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace FiniteLocallyFree

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Lemma 67.46.3: for a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, the following are equivalent: `f` is representable and finite locally free;
`FiniteLocallyFree f`; some scheme `V` with a surjective étale morphism `V ⟶ Y`
has `V ×_Y X ⟶ V` finite locally free; and some Zariski covering `Y = ⋃ Yᵢ` has
each inverse-image morphism `f⁻¹(Yᵢ) ⟶ Yᵢ` finite locally free. -/
@[stacks 03ZW]
theorem tfae :
    List.TFAE [representable f, FiniteLocallyFree f, existsSurjectiveEtaleTarget f,
      existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is finite locally free iff it is representable
and finite locally free in the Section 67.3 sense. -/
theorem iff_representable : FiniteLocallyFree f ↔ representable f := sorry

/-- A morphism of algebraic spaces is finite locally free iff some surjective
étale scheme atlas of the target has finite locally free pullback projection. -/
theorem iff_existsSurjectiveEtaleTarget :
    FiniteLocallyFree f ↔ existsSurjectiveEtaleTarget f := sorry

/-- A morphism of algebraic spaces is finite locally free iff some Zariski
covering of the target has finite locally free inverse images under `f`. -/
theorem iff_existsZariskiCover :
    FiniteLocallyFree f ↔ existsZariskiCover f := sorry

end FiniteLocallyFree

end AlgebraicGeometry.AlgebraicSpace
