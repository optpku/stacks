/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.RepresentedBy
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.PointMap

/-!
# Representability of the relative-spectrum functor

This leaf records affine-local and global representability of the
relative-spectrum functor, together with the canonical comparison from the
explicitly glued model.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- Over an affine base, the relative-spectrum functor is represented by the spectrum of the
global section ring of the algebra sheaf. -/
theorem relativeSpectrumFunctor_isRepresentedBySpecGlobalSections [IsAffine S]
    (A : S.QcAlgebraUnder) :
    ∃ x : (relativeSpectrumFunctor A).obj (op (Spec (qcAlgebraSectionRing A ⊤))),
      (relativeSpectrumFunctor A).IsRepresentedBy x := sorry

/-- The relative-spectrum functor is representable when the base scheme is affine. -/
instance relativeSpectrumFunctor.instIsRepresentableOfIsAffine [IsAffine S]
    (A : S.QcAlgebraUnder) :
    (relativeSpectrumFunctor A).IsRepresentable := sorry

/-- The relative-spectrum functor of a quasi-coherent algebra sheaf is representable. -/
instance relativeSpectrumFunctor.instIsRepresentable (A : S.QcAlgebraUnder) :
    (relativeSpectrumFunctor A).IsRepresentable := sorry

/-- The explicit glued relative-spectrum model represents the relative-spectrum functor via its
universal point. -/
theorem relativeSpectrumFunctor_isRepresentedBy_relativeSpectrumOver (A : S.QcAlgebraUnder) :
    (relativeSpectrumFunctor A).IsRepresentedBy (relativeSpectrumOver A).point := by
  refine ⟨?_⟩
  intro T
  exact (relativeSpectrumHomEquiv A T).bijective

/-- The explicit hom correspondence of the glued model, as representation data.
In particular its inverse is the affine-glued `relativeSpectrumPointMap`, rather than
an inverse selected from a deferred representability proof. -/
def relativeSpectrumRepresentableBy (A : S.QcAlgebraUnder) :
    (relativeSpectrumFunctor A).RepresentableBy (relativeSpectrumOver A).scheme where
  homEquiv := relativeSpectrumHomEquiv A _
  homEquiv_comp f g := by
    exact (relativeSpectrumFunctor A).map_comp_apply g.op f.op (relativeSpectrumOver A).point

/-- The canonical map to a representing scheme is classified by the constructed universal
point of the glued relative spectrum. -/
def relativeSpectrumComparison (A : S.QcAlgebraUnder) {Y : Scheme.{u}}
    (x : relativeSpectrumPair A Y)
    (hx : (relativeSpectrumFunctor A).IsRepresentedBy x) :
    (relativeSpectrumOver A).scheme ⟶ Y :=
  hx.representableBy.homEquiv.symm (relativeSpectrumOver A).point

/-- Pulling back the target universal point gives the constructed universal point. -/
@[simp]
theorem relativeSpectrumComparison_point (A : S.QcAlgebraUnder) {Y : Scheme.{u}}
    (x : relativeSpectrumPair A Y)
    (hx : (relativeSpectrumFunctor A).IsRepresentedBy x) :
    relativeSpectrumPairPullbackMap A (relativeSpectrumComparison A x hx) x =
      (relativeSpectrumOver A).point :=
  hx.representableBy.homEquiv.apply_symm_apply _

/-- The canonical comparison preserves the structure morphisms. -/
theorem relativeSpectrumComparison_toBase (A : S.QcAlgebraUnder) {Y : Scheme.{u}}
    (x : relativeSpectrumPair A Y)
    (hx : (relativeSpectrumFunctor A).IsRepresentedBy x) :
    relativeSpectrumComparison A x hx ≫ x.1 = (relativeSpectrumOver A).π :=
  congrArg Sigma.fst (relativeSpectrumComparison_point A x hx)

/-- The universal point uniquely characterizes the comparison morphism. -/
theorem relativeSpectrumComparison_unique (A : S.QcAlgebraUnder) {Y : Scheme.{u}}
    (x : relativeSpectrumPair A Y)
    (hx : (relativeSpectrumFunctor A).IsRepresentedBy x)
    (f : (relativeSpectrumOver A).scheme ⟶ Y)
    (hf : relativeSpectrumPairPullbackMap A f x = (relativeSpectrumOver A).point) :
    f = relativeSpectrumComparison A x hx := by
  apply hx.representableBy.homEquiv.injective
  exact hf.trans (relativeSpectrumComparison_point A x hx).symm

/-- The explicit affine-glued inverse map classifies the target point. -/
@[simp]
theorem relativeSpectrumPointMap_point (A : S.QcAlgebraUnder) {Y : Scheme.{u}}
    (x : relativeSpectrumPair A Y) :
    relativeSpectrumPairPullbackMap A (relativeSpectrumPointMap A x)
      (relativeSpectrumOver A).point = x :=
  (relativeSpectrumHomEquiv A Y).apply_symm_apply x

/-- The constructed relative spectrum and a scheme with a specified representing point
are canonically isomorphic. Both components are specified, using the explicit source
hom correspondence and the supplied target universal property. -/
def relativeSpectrumRealizationComparisonIso (A : S.QcAlgebraUnder) {Y : Scheme.{u}}
    (x : relativeSpectrumPair A Y)
    (hx : (relativeSpectrumFunctor A).IsRepresentedBy x) :
    (relativeSpectrumOver A).scheme ≅ Y where
  hom := relativeSpectrumComparison A x hx
  inv := relativeSpectrumPointMap A x
  hom_inv_id := by
    apply (relativeSpectrumHomEquiv A _).injective
    change (relativeSpectrumFunctor A).map
        (relativeSpectrumComparison A x hx ≫ relativeSpectrumPointMap A x).op
        (relativeSpectrumOver A).point =
      (relativeSpectrumFunctor A).map (𝟙 _).op (relativeSpectrumOver A).point
    simp only [op_comp, op_id, Functor.map_comp_apply, Functor.map_id_apply]
    change relativeSpectrumPairPullbackMap A (relativeSpectrumComparison A x hx)
        (relativeSpectrumPairPullbackMap A (relativeSpectrumPointMap A x)
          (relativeSpectrumOver A).point) = (relativeSpectrumOver A).point
    rw [relativeSpectrumPointMap_point, relativeSpectrumComparison_point]
  inv_hom_id := by
    apply hx.map_bijective.injective
    change (relativeSpectrumFunctor A).map
        (relativeSpectrumPointMap A x ≫ relativeSpectrumComparison A x hx).op x =
      (relativeSpectrumFunctor A).map (𝟙 _).op x
    simp only [op_comp, op_id, Functor.map_comp_apply, Functor.map_id_apply]
    change relativeSpectrumPairPullbackMap A (relativeSpectrumPointMap A x)
        (relativeSpectrumPairPullbackMap A (relativeSpectrumComparison A x hx) x) = x
    rw [relativeSpectrumComparison_point, relativeSpectrumPointMap_point]

/-- The forward component is precisely the point-classified canonical comparison. -/
@[simp]
theorem relativeSpectrumRealizationComparisonIso_hom (A : S.QcAlgebraUnder)
    {Y : Scheme.{u}} (x : relativeSpectrumPair A Y)
    (hx : (relativeSpectrumFunctor A).IsRepresentedBy x) :
    (relativeSpectrumRealizationComparisonIso A x hx).hom =
      relativeSpectrumComparison A x hx := rfl

/-- The inverse component is the explicit affine-glued map classified by the target point. -/
@[simp]
theorem relativeSpectrumRealizationComparisonIso_inv (A : S.QcAlgebraUnder)
    {Y : Scheme.{u}} (x : relativeSpectrumPair A Y)
    (hx : (relativeSpectrumFunctor A).IsRepresentedBy x) :
    (relativeSpectrumRealizationComparisonIso A x hx).inv =
      relativeSpectrumPointMap A x := rfl

/-- The source-facing comparison is over the base. Its source is the constructed model:
a bare existential `realizesRelativeSpectrum` certificate carries no chosen universal point. -/
def nonempty_iso_over_of_realizesRelativeSpectrum_and_isRepresentedBy
    (A : S.QcAlgebraUnder) {Y : Scheme.{u}} (x : relativeSpectrumPair A Y)
    (hx : (relativeSpectrumFunctor A).IsRepresentedBy x) :
    Over.mk (relativeSpectrumOver A).π ≅ Over.mk x.1 :=
  Over.isoMk (relativeSpectrumRealizationComparisonIso A x hx)
    (relativeSpectrumComparison_toBase A x hx)

@[simp]
theorem nonempty_iso_over_of_realizesRelativeSpectrum_and_isRepresentedBy_hom
    (A : S.QcAlgebraUnder) {Y : Scheme.{u}} (x : relativeSpectrumPair A Y)
    (hx : (relativeSpectrumFunctor A).IsRepresentedBy x) :
    (nonempty_iso_over_of_realizesRelativeSpectrum_and_isRepresentedBy A x hx).hom.left =
      (relativeSpectrumRealizationComparisonIso A x hx).hom := rfl

end AlgebraicGeometry.Scheme
