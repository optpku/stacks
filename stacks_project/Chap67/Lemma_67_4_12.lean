/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap67.Lemma_67_4_12_Local

/-!
# Characterizations of separation axioms for morphisms of algebraic spaces

Lemma 67.4.12 records that a morphism of algebraic spaces is separated, locally
separated, or quasi-separated iff this is tested on scheme-valued and affine
base change, on the absolute separation property of affine pullbacks, on an
étale atlas of the target, and on a Zariski covering of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Separated

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Lemma 67.4.12 (1): for a morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S`, the following are equivalent: `Separated f`; every scheme-valued
base change of `f` is separated; every affine-scheme-valued base change of `f`
is separated; for every affine scheme `Z ⟶ Y` the algebraic space `Z ×_Y X` is
absolutely separated; some surjective étale scheme atlas of `Y` has separated
pullback of `f`; and some Zariski covering of `Y` has each inverse-image
projection `f⁻¹(Yᵢ) ⟶ Yᵢ` separated. -/
@[stacks 03KM]
theorem tfae :
    List.TFAE [Separated f, forallScheme f, forallAffine f, forallAffineSpace f,
      existsEtaleOnTarget f, existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is separated iff every scheme-valued base
change is separated. -/
theorem iff_forallScheme : Separated f ↔ forallScheme f := sorry

/-- A morphism of algebraic spaces is separated iff every affine-scheme-valued
base change is separated. -/
theorem iff_forallAffine : Separated f ↔ forallAffine f := sorry

/-- A morphism of algebraic spaces is separated iff every affine-scheme-valued
pullback object is absolutely separated. -/
theorem iff_forallAffineSpace : Separated f ↔ forallAffineSpace f := sorry

/-- A morphism of algebraic spaces is separated iff some surjective étale scheme
atlas of the target has separated pullback. -/
theorem iff_existsEtaleOnTarget : Separated f ↔ existsEtaleOnTarget f := sorry

/-- A morphism of algebraic spaces is separated iff some Zariski covering of the
target has separated inverse images under `f`. -/
theorem iff_existsZariskiCover : Separated f ↔ existsZariskiCover f := sorry

end Separated

namespace LocallySeparated

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Lemma 67.4.12 (2): for a morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S`, the following are equivalent: `LocallySeparated f`; every
scheme-valued base change of `f` is locally separated; every
affine-scheme-valued base change of `f` is locally separated; for every affine
scheme `Z ⟶ Y` the algebraic space `Z ×_Y X` is absolutely locally separated;
some surjective étale scheme atlas of `Y` has locally separated pullback of `f`;
and some Zariski covering of `Y` has each inverse-image projection
`f⁻¹(Yᵢ) ⟶ Yᵢ` locally separated. -/
@[stacks 03KM]
theorem tfae :
    List.TFAE [LocallySeparated f, forallScheme f, forallAffine f, forallAffineSpace f,
      existsEtaleOnTarget f, existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is locally separated iff every scheme-valued
base change is locally separated. -/
theorem iff_forallScheme : LocallySeparated f ↔ forallScheme f := sorry

/-- A morphism of algebraic spaces is locally separated iff every
affine-scheme-valued base change is locally separated. -/
theorem iff_forallAffine : LocallySeparated f ↔ forallAffine f := sorry

/-- A morphism of algebraic spaces is locally separated iff every
affine-scheme-valued pullback object is absolutely locally separated. -/
theorem iff_forallAffineSpace : LocallySeparated f ↔ forallAffineSpace f := sorry

/-- A morphism of algebraic spaces is locally separated iff some surjective
étale scheme atlas of the target has locally separated pullback. -/
theorem iff_existsEtaleOnTarget : LocallySeparated f ↔ existsEtaleOnTarget f := sorry

/-- A morphism of algebraic spaces is locally separated iff some Zariski
covering of the target has locally separated inverse images under `f`. -/
theorem iff_existsZariskiCover : LocallySeparated f ↔ existsZariskiCover f := sorry

end LocallySeparated

namespace QuasiSeparated

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Lemma 67.4.12 (3): for a morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S`, the following are equivalent: `QuasiSeparated f`; every
scheme-valued base change of `f` is quasi-separated; every
affine-scheme-valued base change of `f` is quasi-separated; for every affine
scheme `Z ⟶ Y` the algebraic space `Z ×_Y X` is absolutely quasi-separated; some
surjective étale scheme atlas of `Y` has quasi-separated pullback of `f`; and
some Zariski covering of `Y` has each inverse-image projection `f⁻¹(Yᵢ) ⟶ Yᵢ`
quasi-separated. -/
@[stacks 03KM]
theorem tfae :
    List.TFAE [QuasiSeparated f, forallScheme f, forallAffine f, forallAffineSpace f,
      existsEtaleOnTarget f, existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is quasi-separated iff every scheme-valued
base change is quasi-separated. -/
theorem iff_forallScheme : QuasiSeparated f ↔ forallScheme f := sorry

/-- A morphism of algebraic spaces is quasi-separated iff every
affine-scheme-valued base change is quasi-separated. -/
theorem iff_forallAffine : QuasiSeparated f ↔ forallAffine f := sorry

/-- A morphism of algebraic spaces is quasi-separated iff every
affine-scheme-valued pullback object is absolutely quasi-separated. -/
theorem iff_forallAffineSpace : QuasiSeparated f ↔ forallAffineSpace f := sorry

/-- A morphism of algebraic spaces is quasi-separated iff some surjective étale
scheme atlas of the target has quasi-separated pullback. -/
theorem iff_existsEtaleOnTarget : QuasiSeparated f ↔ existsEtaleOnTarget f := sorry

/-- A morphism of algebraic spaces is quasi-separated iff some Zariski covering
of the target has quasi-separated inverse images under `f`. -/
theorem iff_existsZariskiCover : QuasiSeparated f ↔ existsZariskiCover f := sorry

end QuasiSeparated

end AlgebraicGeometry.AlgebraicSpace
