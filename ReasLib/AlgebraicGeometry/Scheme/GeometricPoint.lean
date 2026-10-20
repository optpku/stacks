/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import ReasLib.AlgebraicGeometry.Scheme.FieldValuedPoint
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Limits.Elements

open CategoryTheory Opposite

universe u

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- A geometric point of a scheme is a field-valued point whose source field is algebraically
closed. -/
structure GeometricPointObj (S : Scheme.{u}) where
  /-- The underlying field-valued point. -/
  toFieldValuedPoint : FieldValuedPoint S
  /-- The source field of a geometric point is algebraically closed. -/
  isAlgClosed : IsAlgClosed toFieldValuedPoint.K

/-- Geometric points with morphisms induced from their underlying field-valued points. -/
abbrev GeometricPoint (S : Scheme.{u}) :=
  InducedCategory (FieldValuedPoint S) (GeometricPointObj.toFieldValuedPoint (S := S))

namespace GeometricPoint

variable {S : Scheme.{u}}

/-- The underlying field-valued point of a geometric point. -/
def toFieldValuedPoint (s : GeometricPoint S) : FieldValuedPoint S :=
  GeometricPointObj.toFieldValuedPoint s

/-- The source-field carrier of a geometric point. -/
abbrev K (s : GeometricPoint S) : Type u := s.toFieldValuedPoint.K

/-- The field structure of the underlying field-valued point. -/
abbrev field (s : GeometricPoint S) : Field s.K := s.toFieldValuedPoint.field

/-- The stored algebraic closedness of the source field. -/
abbrev isAlgClosed (s : GeometricPoint S) : IsAlgClosed s.K :=
  GeometricPointObj.isAlgClosed s

/-- The morphism from the source-field spectrum of a geometric point to its scheme. -/
abbrev hom (s : GeometricPoint S) : Spec (.of s.K) ⟶ S := s.toFieldValuedPoint.hom

/-- The forgetful functor from geometric points to field-valued points. -/
def toFieldValuedPointFunctor (S : Scheme.{u}) : GeometricPoint S ⥤ FieldValuedPoint S :=
  inducedFunctor GeometricPoint.toFieldValuedPoint

/-- The forgetful functor from geometric points to field-valued points is fully faithful. -/
def toFieldValuedPointFullyFaithful (S : Scheme.{u}) :
    (toFieldValuedPointFunctor S).FullyFaithful :=
  fullyFaithfulInducedFunctor GeometricPoint.toFieldValuedPoint

/-- Construct a geometric point from an algebraically closed field and a morphism from its
spectrum to the scheme. -/
def of (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (.of K) ⟶ S) : GeometricPoint S where
  toFieldValuedPoint := FieldValuedPoint.of K s
  isAlgClosed := inferInstance

/-- The morphism of a geometric point constructed by `of` is the supplied morphism. -/
theorem of_hom (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (.of K) ⟶ S) : (of K s).hom = s := sorry

/-- The image in `S` of the distinguished point of a geometric point. -/
@[reducible] def image (s : GeometricPoint S) : S :=
  s.hom default

/-- The image of a geometric point is defined by evaluating its scheme morphism at the unique
point of the spectrum of its field. -/
theorem image_def (s : GeometricPoint S) : s.image = s.hom default := sorry

/-- The étale neighborhoods of a geometric point, represented by the category of elements of
the lift functor over its scheme morphism. -/
abbrev EtaleNeighborhood (s : GeometricPoint S) :=
  (Etale.forget S ⋙ coyoneda.obj (op (Over.mk s.hom))).Elements

namespace EtaleNeighborhood

/-- The étale scheme underlying an étale neighborhood. -/
abbrev toEtale {s : GeometricPoint S} (U : EtaleNeighborhood s) : S.Etale := U.1

/-- The chosen lift of a geometric point to an étale neighborhood. -/
abbrev lift {s : GeometricPoint S} (U : EtaleNeighborhood s) :
    Spec (.of s.toFieldValuedPoint.K) ⟶ U.toEtale.left := U.2.left

/-- The chosen lift of a geometric point commutes with the étale structure morphism. -/
theorem lift_fac {s : GeometricPoint S} (U : EtaleNeighborhood s) :
    U.lift ≫ U.toEtale.hom = s.hom := sorry

/-- Construct an étale neighborhood from an étale scheme and a lift of the geometric point. -/
def of {s : GeometricPoint S} (U : S.Etale)
    (u : Spec (.of s.toFieldValuedPoint.K) ⟶ U.left)
    (hu : u ≫ U.hom = s.hom) : EtaleNeighborhood s :=
  Functor.elementsMk _ U (Over.homMk u hu)

/-- The chosen lift of the neighborhood constructed by `of` is the supplied lift. -/
theorem of_lift {s : GeometricPoint S} (U : S.Etale)
    (u : Spec (.of s.toFieldValuedPoint.K) ⟶ U.left)
    (hu : u ≫ U.hom = s.hom) : (of U u hu).lift = u := sorry

/-- A morphism of étale neighborhoods is a morphism in the category of elements, hence an
`S`-morphism preserving the chosen lifts. -/
abbrev Hom {s : GeometricPoint S} (V U : EtaleNeighborhood s) := V ⟶ U

namespace Hom

/-- The étale morphism underlying a morphism of étale neighborhoods. -/
abbrev toEtaleHom {s : GeometricPoint S} {V U : EtaleNeighborhood s}
    (f : Hom V U) : V.toEtale ⟶ U.toEtale := f.val

/-- The scheme morphism underlying a morphism of étale neighborhoods. -/
abbrev schemeHom {s : GeometricPoint S} {V U : EtaleNeighborhood s}
    (f : Hom V U) : V.toEtale.left ⟶ U.toEtale.left := f.toEtaleHom.left

/-- A morphism of étale neighborhoods preserves the selected lifts. -/
theorem lift_fac {s : GeometricPoint S} {V U : EtaleNeighborhood s} (f : Hom V U) :
    V.lift ≫ f.schemeHom = U.lift := sorry

/-- The underlying scheme map of a morphism of étale neighborhoods is an `S`-morphism. -/
theorem over_fac {s : GeometricPoint S} {V U : EtaleNeighborhood s} (f : Hom V U) :
    f.schemeHom ≫ U.toEtale.hom = V.toEtale.hom := sorry

/-- Construct a morphism of étale neighborhoods from an étale morphism preserving the selected
lifts. -/
def of {s : GeometricPoint S} {V U : EtaleNeighborhood s}
    (f : V.toEtale ⟶ U.toEtale) (hf : V.lift ≫ f.left = U.lift) : Hom V U :=
  CategoryOfElements.homMk V U f (by
    apply Over.OverMorphism.ext
    exact hf)

/-- The underlying scheme map of the neighborhood morphism constructed by `of` is the supplied
étale morphism. -/
theorem of_schemeHom {s : GeometricPoint S} {V U : EtaleNeighborhood s}
    (f : V.toEtale ⟶ U.toEtale) (hf : V.lift ≫ f.left = U.lift) :
    (of f hf).schemeHom = f.left := sorry

end Hom

end EtaleNeighborhood

end GeometricPoint

end AlgebraicGeometry.Scheme
