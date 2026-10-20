/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.InDimensions
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Square
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ResidueFieldTrdeg
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Flatness in sufficiently large dimensions on algebraic spaces

A quasi-coherent module of finite type on an algebraic space is flat over the
target in dimensions at least `n` when every point of failure of relative
flatness has residue-field transcendence degree less than `n`. This is
equivalent to the corresponding scheme-level condition on some, equivalently
every, étale scheme square, and is preserved by arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A module on an algebraic space is flat over the target in dimensions at least `n`
when every point where relative flatness fails has residue-field transcendence
degree less than `n` over its image. -/
def flatOverInDimensionsGE (ℱ : X.Modules) (f : X ⟶ Y) (n : ℕ) : Prop :=
  ∀ x : Points X, ¬ flatOverAt ℱ f x → residueFieldTranscendenceDegreeAt f x < (n : ℕ∞)

/-- The pointwise residue-field characterization of flatness over the target in
dimensions at least `n`. -/
theorem flatOverInDimensionsGE_iff (ℱ : X.Modules) (f : X ⟶ Y) (n : ℕ) :
    flatOverInDimensionsGE ℱ f n ↔
      ∀ x : Points X, ¬ flatOverAt ℱ f x → residueFieldTranscendenceDegreeAt f x < (n : ℕ∞) :=
  sorry

/-- Flatness over the target in dimensions at least `n` is equivalent to the existence
of a commutative square of schemes with surjective étale vertical arrows along which
the restricted module is flat over the target scheme in dimensions at least `n`. -/
theorem flatOverInDimensionsGE_iff_existsEtaleSquare (ℱ : X.Modules) (f : X ⟶ Y)
    [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (n : ℕ) :
    flatOverInDimensionsGE ℱ f n ↔
      ∃ sq : EtaleSquare f,
        Surjective sq.left.hom ∧ Surjective sq.right.hom ∧
          Scheme.Modules.flatOverInDimensionsGE
            ((restrictFunctor sq.left.hom ⋙ restrictToScheme sq.left.left).obj ℱ) sq.map.left n :=
  sorry

/-- Flatness over the target in dimensions at least `n` is equivalent to the restricted
module being flat over the target scheme in dimensions at least `n` for every
commutative square of schemes with étale vertical arrows. -/
theorem flatOverInDimensionsGE_iff_forallEtaleSquare (ℱ : X.Modules) (f : X ⟶ Y)
    [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (n : ℕ) :
    flatOverInDimensionsGE ℱ f n ↔
      ∀ sq : EtaleSquare f,
        Scheme.Modules.flatOverInDimensionsGE
          ((restrictFunctor sq.left.hom ⋙ restrictToScheme sq.left.left).obj ℱ) sq.map.left n :=
  sorry

/-- Under locally finite type, quasi-coherence, and finite type, the existence of one
surjective étale scheme square with the scheme-level condition is equivalent to the
condition holding for every étale scheme square. -/
theorem flatOverInDimensionsGE_iff_existsEtaleSquare_forall (ℱ : X.Modules)
    (f : X ⟶ Y) [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (n : ℕ) :
    (∃ sq : EtaleSquare f,
        Surjective sq.left.hom ∧ Surjective sq.right.hom ∧
          Scheme.Modules.flatOverInDimensionsGE
            ((restrictFunctor sq.left.hom ⋙ restrictToScheme sq.left.left).obj ℱ) sq.map.left n) ↔
      ∀ sq : EtaleSquare f,
        Scheme.Modules.flatOverInDimensionsGE
          ((restrictFunctor sq.left.hom ⋙ restrictToScheme sq.left.left).obj ℱ) sq.map.left n :=
  sorry

/-- Flatness over the target in dimensions at least `n` is preserved by arbitrary
base change of algebraic spaces. -/
theorem flatOverInDimensionsGE_pullback {Y' : AlgebraicSpace S}
    (ℱ : X.Modules) (f : X ⟶ Y)
    [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (n : ℕ)
    (g : Y' ⟶ Y) :
    flatOverInDimensionsGE ℱ f n →
      flatOverInDimensionsGE ((pullback (Limits.pullback.fst f g)).obj ℱ)
        (Limits.pullback.snd f g) n :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
