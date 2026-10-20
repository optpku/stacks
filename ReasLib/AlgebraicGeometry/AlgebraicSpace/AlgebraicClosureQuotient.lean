/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.NumberTheory.AlgebraicNumbers
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Spectrum
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.FieldPoints
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.GroupAction

/-!
# The spectrum of the algebraic numbers modulo its Galois group

The absolute Galois group of the rationals acts on the spectrum of the complex
algebraic numbers over the rational spectrum. The associated fppf quotient is an
algebraic space whose algebraic field-valued points have only two possible fields.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PreRelation
open AlgebraicNumbers

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient

/-- The spectrum of the rational numbers. -/
abbrev base : Scheme.{0} := Spec (CommRingCat.of ℚ)

/-- The base scheme is the spectrum of the rational numbers. -/
theorem base_eq : base = Spec (CommRingCat.of ℚ) := rfl

/-- The spectrum of the complex algebraic numbers over the rational spectrum. -/
def cover : Over base :=
  Over.mk (FieldExtension.specMap ℚ algebraicQ)

/-- The underlying scheme of the cover is the spectrum of the complex algebraic numbers. -/
theorem cover_left : cover.left = Spec (CommRingCat.of algebraicQ) := rfl

/-- The cover's structure map is induced by the canonical inclusion of the rationals. -/
theorem cover_hom : cover.hom = FieldExtension.specMap ℚ algebraicQ := rfl

/-- Every Galois automorphism of the covering spectrum lies over the rational spectrum. -/
theorem action_w (σ : gal) :
    (FieldExtension.Galois.specAut σ).hom ≫ cover.hom = cover.hom :=
  FieldExtension.Galois.baseAut_over ℚ algebraicQ σ⁻¹

/-- The absolute Galois action on the covering spectrum uses inverse field automorphisms. -/
def action : gal →* Aut cover where
  toFun σ := Over.isoMk (FieldExtension.Galois.specAut σ) (action_w σ)
  map_one' := by
    apply Aut.ext
    apply Over.OverMorphism.ext
    change (FieldExtension.Galois.specAut (1 : gal)).hom = 𝟙 _
    exact congrArg Iso.hom
      (map_one (FieldExtension.Galois.specAut (k := ℚ) (k' := algebraicQ)))
  map_mul' σ τ := by
    apply Aut.ext
    apply Over.OverMorphism.ext
    change (FieldExtension.Galois.specAut (σ * τ)).hom =
      (FieldExtension.Galois.specAut τ).hom ≫ (FieldExtension.Galois.specAut σ).hom
    exact congrArg Iso.hom
      (map_mul (FieldExtension.Galois.specAut (k := ℚ) (k' := algebraicQ)) σ τ)

/-- The underlying spectrum map of a Galois element is induced by its inverse. -/
theorem action_hom (σ : gal) :
    (action σ).hom.left = FieldExtension.Galois.baseAut ℚ algebraicQ σ⁻¹ := rfl

/-- The identity Galois element acts as the identity automorphism of the cover. -/
theorem action_one : action 1 = 1 := action.map_one

/-- The absolute Galois action on the covering spectrum is residue-field free. -/
instance instIsResidueFieldFree_action : IsResidueFieldFree action := sorry

/-- The fppf quotient sheaf of the covering spectrum by its absolute Galois action. -/
def sheafOfPoints : Sheaf (Scheme.fppfTopology.over base) (Type 1) :=
  (ofAut action).quotientSheaf (Scheme.fppfTopology.over base)

/-- The quotient sheaf is the sheafification of the Galois orbit presheaf. -/
theorem sheafOfPoints_eq :
    sheafOfPoints = (ofAut action).quotientSheaf (Scheme.fppfTopology.over base) := rfl

/-- The canonical map from the represented covering spectrum to its fppf quotient. -/
def atlas :
    (Scheme.fppfTopology.over base).uliftYoneda.{1}.obj cover ⟶ sheafOfPoints :=
  (ofAut action).quotientMap (Scheme.fppfTopology.over base)

/-- The atlas is the canonical fppf quotient map of the Galois orbit relation. -/
theorem atlas_eq : atlas = (ofAut action).quotientMap (Scheme.fppfTopology.over base) := rfl

/-- The quotient has a representable diagonal and a representable étale atlas that is
locally surjective for the étale topology. -/
theorem sheafOfPoints_spec :
    uliftYoneda.{1}.relativelyRepresentable (diag sheafOfPoints.obj) ∧
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{1} atlas.hom ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over base) atlas.hom :=
  quotientSheaf_spec_ofAut action

/-- An algebraic extension of the rationals with a point of the absolute Galois quotient
is rationally isomorphic to the complex algebraic numbers or the real algebraic numbers. -/
theorem eq_algebraicQ_or_realIntersection {k : Type} [Field k] [Algebra ℚ k]
    [Algebra.IsAlgebraic ℚ k] (f : specToQuotientHom action (FieldExtension.specMap ℚ k)) :
    Nonempty (k ≃ₐ[ℚ] algebraicQ) ∨ Nonempty (k ≃ₐ[ℚ] realIntersection) := sorry

end AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient
