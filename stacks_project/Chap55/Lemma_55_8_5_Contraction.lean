/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap55.Lemma_55_8_5_Model
public import stacks_project.Chap54.Lemma_54_16_3_ExceptionalCurve
public import stacks_project.Chap54.Lemma_54_16_4_Contraction

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

/-- A contraction step between regular models, including its exceptional curve and
compatibility with the structural morphisms and generic-fibre identifications. -/
structure ContractionStep.{u} {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (source target : RegularModel R K C) where
  /-- The morphism from the source model to the target model. -/
  morphism : source.scheme ⟶ target.scheme
  /-- The exceptional ideal sheaf on the source model. -/
  exceptionalIdeal : source.scheme.IdealSheafData
  /-- The exceptional ideal defines a curve of the first kind. -/
  exceptional : IsExceptionalCurveFirstKind exceptionalIdeal
  /-- The closed point contracted by the morphism. -/
  center : closedPoints target.scheme
  /-- The morphism contracts the chosen exceptional curve to the chosen center. -/
  contraction : @IsContraction source.scheme target.scheme source.isNoetherian
    exceptionalIdeal exceptional morphism center
  /-- The contraction is a morphism over the base. -/
  over : morphism ≫ target.base = source.base
  /-- On the generic fibre, the contraction is the identity under the chosen
  identifications with the curve. -/
  genericFiber_identity :
    source.genericFiberIso.hom ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
          (Over.homMk morphism over : Over.mk source.base ⟶ Over.mk target.base) =
      target.genericFiberIso.hom

universe u

namespace ContractionStep

/-- Construct a contraction step from its morphism, exceptional-curve data, and compatibility law. -/
def ofData {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    {source target : RegularModel R K C} (morphism : source.scheme ⟶ target.scheme)
    (exceptionalIdeal : source.scheme.IdealSheafData)
    (h_exceptional : IsExceptionalCurveFirstKind exceptionalIdeal)
    (center : closedPoints target.scheme)
    (h_contraction : @IsContraction source.scheme target.scheme source.isNoetherian
      exceptionalIdeal h_exceptional morphism center)
    (h_over : morphism ≫ target.base = source.base)
    (h_genericFiber :
      source.genericFiberIso.hom ≫
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
            (Over.homMk morphism h_over : Over.mk source.base ⟶ Over.mk target.base) =
        target.genericFiberIso.hom) : ContractionStep source target :=
  { morphism := morphism
    exceptionalIdeal := exceptionalIdeal
    exceptional := h_exceptional
    center := center
    contraction := h_contraction
    over := h_over
    genericFiber_identity := h_genericFiber }

end ContractionStep

end AlgebraicGeometry.Scheme.Hom
