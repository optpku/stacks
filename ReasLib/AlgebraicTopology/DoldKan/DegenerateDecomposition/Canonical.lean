/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.DoldKan.QInftyImage
public import ReasLib.AlgebraicTopology.DoldKan.Normalized
public import ReasLib.Algebra.Homology.HomologicalComplex.Biproduct
public import ReasLib.CategoryTheory.Limits.BinaryBiproduct.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical image decomposition of the Dold--Kan complex

This leaf owns the decomposition of the alternating-face complex into the normalized Moore
complex and the image of the complementary `QInfty` projector.  The degreewise degenerate
presentation and its comparison with this image are provided by sibling leaves.

@stack 019A
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open scoped Simplicial DoldKan

noncomputable section

universe v u

namespace AlgebraicTopology.DoldKan

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace QInfty

namespace decomposition

/-- The canonical map from the alternating-face complex to its normalized and projector-image
coordinates. -/
@[stacks 019A "canonical normalized-projector-image decomposition map"]
noncomputable def hom (U : SimplicialObject A) : K[U] ⟶ N[U] ⊞ QInfty.image U :=
  biprod.lift (PInftyToNormalizedMooreComplex U) (QInfty.toImage U)

/-- The canonical map reconstructing the alternating-face complex from its normalized and
projector-image coordinates. -/
@[stacks 019A "canonical normalized-projector-image reconstruction map"]
noncomputable def inv (U : SimplicialObject A) : N[U] ⊞ QInfty.image U ⟶ K[U] :=
  biprod.desc (inclusionOfMooreComplexMap U) (QInfty.fromImage U)

/-- The canonical normalized and projector-image coordinates reconstruct the alternating-face
complex. -/
@[reassoc, stacks 019A "canonical normalized-projector-image decomposition inverse law"]
theorem hom_comp_inv (U : SimplicialObject A) :
    decomposition.hom U ≫ decomposition.inv U = 𝟙 K[U] := sorry

/-- Reconstructing from the canonical normalized and projector-image summands and then taking
coordinates is the identity. -/
@[reassoc, stacks 019A "canonical normalized-projector-image decomposition inverse law"]
theorem inv_comp_hom (U : SimplicialObject A) :
    decomposition.inv U ≫ decomposition.hom U = 𝟙 (N[U] ⊞ QInfty.image U) := sorry

end decomposition

/-- The canonical Dold--Kan splitting into the normalized Moore complex and the image of the
complementary projector. -/
@[stacks 019A "canonical Dold-Kan normalized-projector-image decomposition"]
noncomputable def decomposition (U : SimplicialObject A) :
    K[U] ≅ N[U] ⊞ QInfty.image U where
  hom := decomposition.hom U
  inv := decomposition.inv U
  hom_inv_id := decomposition.hom_comp_inv U
  inv_hom_id := decomposition.inv_comp_hom U

namespace decomposition

/-- The forward canonical decomposition map is the pair of normalized and projector-image
projections. -/
@[stacks 019A "canonical normalized-projector-image decomposition forward map"]
theorem hom_eq (U : SimplicialObject A) :
    (QInfty.decomposition U).hom = decomposition.hom U := sorry

/-- The inverse canonical decomposition map is induced by the normalized and projector-image
inclusions. -/
@[stacks 019A "canonical normalized-projector-image decomposition inverse map"]
theorem inv_eq (U : SimplicialObject A) :
    (QInfty.decomposition U).inv = decomposition.inv U := sorry

/-- The named canonical decomposition map is the explicit biproduct lift. -/
@[simp, stacks 019A "canonical normalized-projector-image decomposition map formula"]
theorem hom_def (U : SimplicialObject A) :
    decomposition.hom U =
      biprod.lift (PInftyToNormalizedMooreComplex U) (QInfty.toImage U) := sorry

/-- The named canonical reconstruction map is the explicit biproduct descent. -/
@[simp, stacks 019A "canonical normalized-projector-image reconstruction map formula"]
theorem inv_def (U : SimplicialObject A) :
    decomposition.inv U =
      biprod.desc (inclusionOfMooreComplexMap U) (QInfty.fromImage U) := sorry

/-- The normalized inclusion is the left biproduct inclusion in the canonical decomposition. -/
@[reassoc, stacks 019A "canonical decomposition normalized inclusion coordinate"]
theorem inclusion_comp_hom (U : SimplicialObject A) :
    inclusionOfMooreComplexMap U ≫ (QInfty.decomposition U).hom = biprod.inl := sorry

/-- The normalized projection is the left coordinate of the canonical decomposition. -/
@[reassoc, stacks 019A "canonical normalized-projector-image decomposition projection coordinate"]
theorem hom_comp_fst (U : SimplicialObject A) :
    (QInfty.decomposition U).hom ≫ biprod.fst =
      PInftyToNormalizedMooreComplex U := sorry

/-- The projection to `QInfty.image` is the right coordinate of the canonical decomposition. -/
@[reassoc, stacks 019A "canonical normalized-projector-image decomposition image projection"]
theorem hom_comp_snd (U : SimplicialObject A) :
    (QInfty.decomposition U).hom ≫ biprod.snd = QInfty.toImage U := sorry

/-- The inclusion from `QInfty.image` is the right biproduct inclusion in the canonical
decomposition. -/
@[reassoc, stacks 019A "canonical normalized-projector-image decomposition image inclusion"]
theorem fromImage_comp_hom (U : SimplicialObject A) :
    QInfty.fromImage U ≫ (QInfty.decomposition U).hom = biprod.inr := sorry

/-- The inverse canonical decomposition restricts to the normalized inclusion on the left
summand. -/
@[reassoc, stacks 019A "canonical inverse decomposition normalized coordinate"]
theorem inl_comp_inv (U : SimplicialObject A) :
    biprod.inl ≫ (QInfty.decomposition U).inv = inclusionOfMooreComplexMap U := sorry

/-- The inverse canonical decomposition restricts to the projector-image inclusion on the right
summand. -/
@[reassoc, stacks 019A "canonical inverse decomposition image coordinate"]
theorem inr_comp_inv (U : SimplicialObject A) :
    biprod.inr ≫ (QInfty.decomposition U).inv = QInfty.fromImage U := sorry

/-- The normalized inclusion has zero component in the canonical projector-image summand. -/
@[reassoc, stacks 019A "normalized inclusion annihilates the projector image"]
theorem inclusion_comp_toImage (U : SimplicialObject A) :
    inclusionOfMooreComplexMap U ≫ QInfty.toImage U = 0 := sorry

/-- The canonical projector-image inclusion has zero component in the normalized Moore summand. -/
@[reassoc, stacks 019A "projector-image inclusion annihilates the normalized projection"]
theorem fromImage_comp_projection (U : SimplicialObject A) :
    QInfty.fromImage U ≫ PInftyToNormalizedMooreComplex U = 0 := sorry

/-- The normalized and canonical projector-image projectors sum to the identity on the
alternating-face complex. -/
@[stacks 019A "normalized-projector-image projector sum"]
theorem projector_sum (U : SimplicialObject A) :
    (PInftyToNormalizedMooreComplex U ≫ inclusionOfMooreComplexMap U : K[U] ⟶ K[U]) +
        QInfty.toImage U ≫ QInfty.fromImage U = 𝟙 K[U] := sorry

/-- The natural projection to the normalized and canonical projector-image summands. -/
@[stacks 019A "canonical normalized-projector-image decomposition projection"]
noncomputable def toSummand :
    alternatingFaceMapComplex A ⟶
      (normalizedMooreComplex A) ⊞ QInfty.imageFunctor (C := A) :=
  biprod.lift (projectionToMooreComplex A) (QInfty.toImage.natTrans (C := A))

/-- The natural comparison from the normalized and canonical projector-image summands. -/
@[stacks 019A "canonical normalized-projector-image decomposition comparison"]
noncomputable def fromSummand :
    (normalizedMooreComplex A) ⊞ QInfty.imageFunctor (C := A) ⟶
      alternatingFaceMapComplex A :=
  biprod.desc (inclusionOfMooreComplex A) (QInfty.fromImage.natTrans (C := A))

/-- The canonical decomposition projection followed by its comparison is the identity. -/
@[stacks 019A "canonical normalized-projector-image decomposition inverse law"]
theorem to_comp_from :
    toSummand (A := A) ≫ fromSummand (A := A) =
      𝟙 (alternatingFaceMapComplex A) := sorry

/-- The canonical comparison followed by the decomposition projection is the identity. -/
@[stacks 019A "canonical normalized-projector-image decomposition inverse law"]
theorem from_comp_to :
    fromSummand (A := A) ≫ toSummand (A := A) =
      𝟙 ((normalizedMooreComplex A) ⊞ QInfty.imageFunctor (C := A)) := sorry

/-- The canonical Dold--Kan decomposition as a natural isomorphism. -/
@[stacks 019A "canonical normalized-projector-image decomposition natural isomorphism"]
noncomputable def natIso :
    alternatingFaceMapComplex A ≅
      (normalizedMooreComplex A) ⊞ QInfty.imageFunctor (C := A) where
  hom := toSummand
  inv := fromSummand
  hom_inv_id := to_comp_from
  inv_hom_id := from_comp_to

/-- The evaluation of the functorial biproduct target is identified with the objectwise target. -/
@[stacks 019A "evaluation bridge for the canonical Dold-Kan decomposition target"]
noncomputable def evalIso (U : SimplicialObject A) :
    ((normalizedMooreComplex A) ⊞ QInfty.imageFunctor (C := A)).obj U ≅
      N[U] ⊞ QInfty.image U :=
  CategoryTheory.Limits.evalBiprodIso (normalizedMooreComplex A)
    (QInfty.imageFunctor (C := A)) U

/-- After the evaluation bridge, the functorial canonical decomposition is the objectwise one. -/
@[stacks 019A "component of the canonical Dold-Kan decomposition"]
theorem natIso.app (U : SimplicialObject A) :
    (natIso (A := A)).app U ≪≫ evalIso U = QInfty.decomposition U := sorry

/-- The forward evaluated canonical decomposition is the objectwise forward decomposition map. -/
@[stacks 019A "forward canonical decomposition component"]
theorem natIso.hom_app (U : SimplicialObject A) :
    (natIso (A := A)).hom.app U ≫ (evalIso U).hom =
      (QInfty.decomposition U).hom := sorry

/-- The inverse of the evaluated canonical decomposition is the inverse evaluation bridge followed
by the inverse functor-category component. -/
@[stacks 019A "inverse canonical decomposition component"]
theorem natIso.inv_app (U : SimplicialObject A) :
    (evalIso U).inv ≫ (natIso (A := A)).inv.app U = (QInfty.decomposition U).inv := sorry

/-- The left coordinate of the natural canonical decomposition is the normalized projection. -/
@[reassoc, stacks 019A "canonical functorial decomposition normalized coordinate"]
theorem toSummand.app_fst (U : SimplicialObject A) :
    (toSummand (A := A)).app U ≫
      ((biprod.fst : (normalizedMooreComplex A) ⊞ QInfty.imageFunctor (C := A) ⟶
        normalizedMooreComplex A).app U) = PInftyToNormalizedMooreComplex U := sorry

/-- The right coordinate of the natural canonical decomposition is the projection to `QInfty.image`.
-/
@[reassoc, stacks 019A "canonical functorial decomposition image coordinate"]
theorem toSummand.app_snd (U : SimplicialObject A) :
    (toSummand (A := A)).app U ≫
      ((biprod.snd : (normalizedMooreComplex A) ⊞ QInfty.imageFunctor (C := A) ⟶
        QInfty.imageFunctor (C := A)).app U) = QInfty.toImage U := sorry

/-- The natural canonical comparison restricts to the normalized inclusion on the left. -/
@[reassoc, stacks 019A "canonical functorial comparison normalized coordinate"]
theorem fromSummand.inl_app (U : SimplicialObject A) :
    ((biprod.inl : normalizedMooreComplex A ⟶
        (normalizedMooreComplex A) ⊞ QInfty.imageFunctor (C := A)).app U) ≫
      (fromSummand (A := A)).app U = inclusionOfMooreComplexMap U := sorry

/-- The natural canonical comparison restricts to the `QInfty` image inclusion on the right. -/
@[reassoc, stacks 019A "canonical functorial comparison image coordinate"]
theorem fromSummand.inr_app (U : SimplicialObject A) :
    ((biprod.inr : QInfty.imageFunctor (C := A) ⟶
        (normalizedMooreComplex A) ⊞ QInfty.imageFunctor (C := A)).app U) ≫
      (fromSummand (A := A)).app U = QInfty.fromImage U := sorry

/-- The forward map of the natural canonical decomposition is its projection. -/
@[simp, stacks 019A "canonical functorial Dold-Kan decomposition forward map"]
theorem natIso.hom_eq :
    (natIso (A := A)).hom = toSummand (A := A) := sorry

/-- The inverse map of the natural canonical decomposition is its comparison. -/
@[simp, stacks 019A "canonical functorial Dold-Kan decomposition inverse map"]
theorem natIso.inv_eq :
    (natIso (A := A)).inv = fromSummand (A := A) := sorry

end decomposition

end QInfty

end AlgebraicTopology.DoldKan
