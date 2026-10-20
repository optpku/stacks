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
public import ReasLib.AlgebraicGeometry.FormalSpectrum.WeakIdeal
public import ReasLib.AlgebraicGeometry.FormalSpectrum.QuotientDiagram

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
  ⟨rfl, h⟩

namespace PresheafFormalSpectrum

/-- The formal spectrum of a weakly admissible ring over `S`, as the colimit of
the Yoneda embeddings of its weak-ideal thickenings. -/
def spf (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S) : (Over S)ᵒᵖ ⥤ Type u :=
  colimit (thickenings A structureHom ⋙ yoneda)

/-- Functor-of-points data of an affine formal algebraic space: a directed
diagram of affine stages with thickening transitions whose Yoneda colimit is
`X`. -/
def IsDirectedAffineYonedaColimit {S : Scheme.{u}} {Λ : Type u} [Preorder Λ]
    (D : Λ ⥤ Over S) (X : (Over S)ᵒᵖ ⥤ Type u) : Prop :=
  IsDirected Λ (· ≤ ·) ∧
    (∀ I, IsAffine (D.obj I).left) ∧
      (∀ {I J : Λ} (f : I ⟶ J), IsThickening (D.map f).left) ∧
        ∃ c : Cocone (D ⋙ yoneda), c.pt = X ∧ Nonempty (IsColimit c)

/-- The residue-field stage `Spec(κ) ⟶ Spf(A)` corresponding to a proof that
the maximal ideal is a weak ideal of definition. -/
def specResidue (A : Type u) [CommRing A] [IsLocalRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S)
    (h : TopologicalRing.Ideal.IsWeakIdealOfDefinition (maximalIdeal A)) :
    yoneda.obj (stage A structureHom (WeakIdealOfDefinition.maximal h)) ⟶
      spf A structureHom :=
  colimit.ι (thickenings A structureHom ⋙ yoneda) (WeakIdealOfDefinition.maximal h)

/-- The stage at the maximal ideal is `Spec` of the residue field. -/
theorem stage_maximal_left (A : Type u) [CommRing A] [IsLocalRing A] [TopologicalSpace A]
    {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    (h : TopologicalRing.Ideal.IsWeakIdealOfDefinition (maximalIdeal A)) :
    (stage A structureHom (WeakIdealOfDefinition.maximal h)).left =
      Spec (.of (ResidueField A)) :=
  sorry

end PresheafFormalSpectrum

end AlgebraicGeometry.AffineFormalAlgebraicSpace
