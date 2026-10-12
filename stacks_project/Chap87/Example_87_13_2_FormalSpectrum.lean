/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Order.Directed
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import stacks_project.Chap87.Definition_87_4_8_WeaklyAdmissible

/-!
# Formal spectra along weak ideals of definition

The functor-of-points formal spectrum of a weakly admissible ring `A` over a
scheme `S` is the colimit of `yoneda.obj (Spec(A ⧸ I))` as `I` runs over weak
ideals of definition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- A weak ideal of definition, bundled as an index for the formal spectrum. -/
structure WeakIdealOfDefinition (A : Type u) [CommRing A] [TopologicalSpace A] where
  /-- Underlying ideal. -/
  ideal : Ideal A
  /-- The ideal is a weak ideal of definition. -/
  isWeak : TopologicalRing.Ideal.IsWeakIdealOfDefinition ideal

/-- Bundle an ideal with a proof that it is a weak ideal of definition. -/
def WeakIdealOfDefinition.of {A : Type u} [CommRing A] [TopologicalSpace A] (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I) : WeakIdealOfDefinition A where
  ideal := I
  isWeak := hI

/-- The smart constructor recovers the underlying ideal and the weak-ideal
property. -/
theorem WeakIdealOfDefinition.of_spec {A : Type u} [CommRing A] [TopologicalSpace A]
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I) :
    (WeakIdealOfDefinition.of I hI).ideal = I ∧
      TopologicalRing.Ideal.IsWeakIdealOfDefinition (WeakIdealOfDefinition.of I hI).ideal :=
  sorry

/-- The maximal ideal, viewed as a weak ideal of definition once that property
is supplied. -/
def WeakIdealOfDefinition.maximal {A : Type u} [CommRing A] [IsLocalRing A]
    [TopologicalSpace A]
    (h : TopologicalRing.Ideal.IsWeakIdealOfDefinition (maximalIdeal A)) :
    WeakIdealOfDefinition A :=
  WeakIdealOfDefinition.of (maximalIdeal A) h

/-- The bundled maximal ideal recovers `maximalIdeal A` and the supplied
weak-ideal property. -/
theorem WeakIdealOfDefinition.maximal_spec {A : Type u} [CommRing A] [IsLocalRing A]
    [TopologicalSpace A]
    (h : TopologicalRing.Ideal.IsWeakIdealOfDefinition (maximalIdeal A)) :
    (WeakIdealOfDefinition.maximal h).ideal = maximalIdeal A ∧
      TopologicalRing.Ideal.IsWeakIdealOfDefinition
        (WeakIdealOfDefinition.maximal h).ideal :=
  sorry

variable {A : Type u} [CommRing A] [TopologicalSpace A]

/-- Reverse inclusion of underlying ideals, so that `J ≤ I` yields
`Spec(A ⧸ J) ⟶ Spec(A ⧸ I)`. -/
instance : Preorder (WeakIdealOfDefinition A) where
  le I J := J.ideal ≤ I.ideal
  le_refl := sorry
  le_trans := sorry

/-- The reverse-inclusion order on weak ideals of definition is directed. -/
instance : IsDirected (WeakIdealOfDefinition A) (· ≤ ·) :=
  sorry

/-- Reverse inclusion unpacks as inclusion of underlying ideals. -/
theorem WeakIdealOfDefinition.le_iff {I J : WeakIdealOfDefinition A} :
    I ≤ J ↔ J.ideal ≤ I.ideal :=
  sorry

/-- The affine stage `Spec(A ⧸ I)` over `S`. -/
def stage (A : Type u) [CommRing A] [TopologicalSpace A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S) (I : WeakIdealOfDefinition A) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I.ideal)) ≫ structureHom)

/-- The underlying scheme of `stage A structureHom I` is `Spec(A ⧸ I)`. -/
theorem stage_left (A : Type u) [CommRing A] [TopologicalSpace A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S) (I : WeakIdealOfDefinition A) :
    (stage A structureHom I).left = Spec (.of (A ⧸ I.ideal)) :=
  sorry

/-- The diagram of affine thickenings `Spec(A ⧸ I)` indexed by weak ideals of
definition. -/
def thickenings (A : Type u) [CommRing A] [TopologicalSpace A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S) : WeakIdealOfDefinition A ⥤ Over S where
  obj I := stage A structureHom I
  map {I J} f :=
    Over.homMk
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (leOfHom f : J.ideal ≤ I.ideal))))
      sorry
  map_id := sorry
  map_comp := sorry

/-- Objects of `thickenings A structureHom` are the stages `stage A structureHom I`. -/
theorem thickenings_obj (A : Type u) [CommRing A] [TopologicalSpace A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S) (I : WeakIdealOfDefinition A) :
    (thickenings A structureHom).obj I = stage A structureHom I :=
  sorry

/-- Each stage `Spec(A ⧸ I)` is affine. -/
instance thickenings_obj_isAffine (A : Type u) [CommRing A] [TopologicalSpace A]
    {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S) (I : WeakIdealOfDefinition A) :
    IsAffine (stage A structureHom I).left :=
  sorry

/-- Transition maps of `thickenings A structureHom` are thickenings. -/
instance thickenings_map_isThickening (A : Type u) [CommRing A] [TopologicalSpace A]
    {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S) {I J : WeakIdealOfDefinition A}
    (f : I ⟶ J) : IsThickening ((thickenings A structureHom).map f).left :=
  sorry

/-- The formal spectrum of a weakly admissible ring over `S`, as the colimit of
the Yoneda embeddings of its weak-ideal thickenings. -/
def spf (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S) : (Over S)ᵒᵖ ⥤ Type u :=
  colimit (thickenings A structureHom ⋙ yoneda)

/-- `spf A structureHom` is the colimit of the Yoneda diagram of
`thickenings A structureHom`. -/
theorem spf_eq (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S) :
    spf A structureHom = colimit (thickenings A structureHom ⋙ yoneda) :=
  sorry

/-- Functor-of-points data of an affine formal algebraic space: a directed
diagram of affine stages with thickening transitions whose Yoneda colimit is
`X`. -/
def IsDirectedAffineYonedaColimit {S : Scheme.{u}} {Λ : Type u} [Preorder Λ]
    (D : Λ ⥤ Over S) (X : (Over S)ᵒᵖ ⥤ Type u) : Prop :=
  IsDirected Λ (· ≤ ·) ∧
    (∀ I, IsAffine (D.obj I).left) ∧
      (∀ {I J : Λ} (f : I ⟶ J), IsThickening (D.map f).left) ∧
        ∃ c : Cocone (D ⋙ yoneda), c.pt = X ∧ Nonempty (IsColimit c)

/-- Unpacking of `IsDirectedAffineYonedaColimit`. -/
theorem IsDirectedAffineYonedaColimit_iff {S : Scheme.{u}} {Λ : Type u}
    [Preorder Λ] (D : Λ ⥤ Over S) (X : (Over S)ᵒᵖ ⥤ Type u) :
    IsDirectedAffineYonedaColimit D X ↔
      IsDirected Λ (· ≤ ·) ∧
        (∀ I, IsAffine (D.obj I).left) ∧
          (∀ {I J : Λ} (f : I ⟶ J), IsThickening (D.map f).left) ∧
            ∃ c : Cocone (D ⋙ yoneda), c.pt = X ∧ Nonempty (IsColimit c) :=
  sorry

/-- The residue-field stage `Spec(κ) ⟶ Spf(A)` corresponding to a proof that
the maximal ideal is a weak ideal of definition. -/
def specResidue (A : Type u) [CommRing A] [IsLocalRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S)
    (h : TopologicalRing.Ideal.IsWeakIdealOfDefinition (maximalIdeal A)) :
    yoneda.obj (stage A structureHom (WeakIdealOfDefinition.maximal h)) ⟶
      spf A structureHom :=
  colimit.ι (thickenings A structureHom ⋙ yoneda) (WeakIdealOfDefinition.maximal h)

/-- `specResidue` is the colimit cocone component at the maximal ideal. -/
theorem specResidue_eq (A : Type u) [CommRing A] [IsLocalRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S)
    (h : TopologicalRing.Ideal.IsWeakIdealOfDefinition (maximalIdeal A)) :
    specResidue A structureHom h =
      colimit.ι (thickenings A structureHom ⋙ yoneda)
        (WeakIdealOfDefinition.maximal h) :=
  sorry

/-- The stage at the maximal ideal is `Spec` of the residue field. -/
theorem stage_maximal_left (A : Type u) [CommRing A] [IsLocalRing A] [TopologicalSpace A]
    {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    (h : TopologicalRing.Ideal.IsWeakIdealOfDefinition (maximalIdeal A)) :
    (stage A structureHom (WeakIdealOfDefinition.maximal h)).left =
      Spec (.of (ResidueField A)) :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
