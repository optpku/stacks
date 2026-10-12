/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.Normalized.Quotient
public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.Normalized.Moore

/-!
# Comparison of normalized cochain models

This leaf compares the quotient-defined normalized complex with the transported normalized Moore
complex and exposes the quotient section independently of the resulting equivalence.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits
open AlgebraicTopology
open AlgebraicTopology.DoldKan

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace normalizedMooreCochainComplex

/-- The transported normalized projection annihilates the source-facing degenerate inclusion. -/
@[reassoc, stacks 019I "transported normalized projection annihilates source degeneracies"]
theorem degenerate_ι_comp_π (U : CosimplicialObject A) :
    degenerateCochainComplex.ι U ≫ π U = 0 := sorry

end normalizedMooreCochainComplex

namespace normalizedCochainComplex

/-- The comparison from the transported normalized Moore model to the quotient-defined
normalized cochain complex. -/
@[stacks 019I "normalized cochain comparison map to quotient"]
def comparison.toQuotient (U : CosimplicialObject A) :
    normalizedMooreCochainComplex U ⟶ normalizedCochainComplex U :=
  normalizedMooreCochainComplex.ι U ≫ π U

/-- The map from quotient-defined normalized cochains to the transported normalized Moore model,
obtained by the cokernel universal property. -/
@[stacks 019I "normalized cochain comparison map to transported Moore complex"]
def comparison.toMoore (U : CosimplicialObject A) :
    normalizedCochainComplex U ⟶ normalizedMooreCochainComplex U :=
  desc U (normalizedMooreCochainComplex.π U)
    (normalizedMooreCochainComplex.degenerate_ι_comp_π U)

/-- The cokernel-descended map recovers the transported normalized projection after the quotient
map. -/
@[reassoc, stacks 019I "normalized cochain comparison projection formula"]
theorem comparison.π_comp_toMoore (U : CosimplicialObject A) :
    π U ≫ comparison.toMoore U = normalizedMooreCochainComplex.π U := sorry

/-- The comparison followed by its explicit cokernel-descended inverse is the identity. -/
@[stacks 019I "normalized cochain comparison inverse law"]
theorem comparison.hom_comp_inv (U : CosimplicialObject A) :
    comparison.toQuotient U ≫ comparison.toMoore U = 𝟙 _ := sorry

/-- The explicit cokernel-descended inverse followed by the comparison is the identity. -/
@[stacks 019I "normalized cochain comparison inverse law"]
theorem comparison.inv_comp_hom (U : CosimplicialObject A) :
    comparison.toMoore U ≫ comparison.toQuotient U = 𝟙 _ := sorry

/-- The objectwise comparison between the transported normalized Moore model and the
quotient-defined normalized cochain complex. -/
@[stacks 019I "normalized cochain comparison"]
def comparison.iso (U : CosimplicialObject A) :
    normalizedMooreCochainComplex U ≅ normalizedCochainComplex U where
  hom := comparison.toQuotient U
  inv := comparison.toMoore U
  hom_inv_id := comparison.hom_comp_inv U
  inv_hom_id := comparison.inv_comp_hom U

/-- The forward map of the comparison is the explicit map from the transported Moore model to the
quotient. -/
@[simp, stacks 019I "normalized cochain comparison forward map"]
theorem comparison.hom_eq (U : CosimplicialObject A) :
    (comparison.iso U).hom = comparison.toQuotient U := sorry

/-- The inverse map of the comparison is the explicit cokernel descent to the transported Moore
model. -/
@[simp, stacks 019I "normalized cochain comparison inverse map"]
theorem comparison.inv_eq (U : CosimplicialObject A) :
    (comparison.iso U).inv = comparison.toMoore U := sorry

/-- The forward comparison to the quotient-defined model is natural in the cosimplicial object. -/
@[reassoc, stacks 019I "normalized cochain forward comparison naturality"]
theorem comparison.toQuotient.naturality {U V : CosimplicialObject A} (f : U ⟶ V) :
    normalizedMooreCochainComplex.functor.map f ≫ comparison.toQuotient V =
      comparison.toQuotient U ≫ normalizedCochainComplex.functor.map f := sorry

/-- The inverse comparison to the transported Moore model is natural in the cosimplicial object. -/
@[reassoc, stacks 019I "normalized cochain inverse comparison naturality"]
theorem comparison.toMoore.naturality {U V : CosimplicialObject A} (f : U ⟶ V) :
    normalizedCochainComplex.functor.map f ≫ comparison.toMoore V =
      comparison.toMoore U ≫ normalizedMooreCochainComplex.functor.map f := sorry

/-- Naturality of the comparison with the quotient-defined normalized cochain complex. -/
@[reassoc, stacks 019I "normalized cochain comparison naturality"]
theorem comparison.naturality {U V : CosimplicialObject A} (f : U ⟶ V) :
    normalizedMooreCochainComplex.functor.map f ≫ (comparison.iso V).hom =
      (comparison.iso U).hom ≫ normalizedCochainComplex.functor.map f := sorry

/-- The transported normalized Moore functor is naturally isomorphic to the quotient-defined
normalized cochain complex functor. -/
@[stacks 019I "normalized cochain comparison natural isomorphism"]
def comparison.natIso :
    normalizedMooreCochainComplex.functor (A := A) ≅
      normalizedCochainComplex.functor (A := A) :=
  NatIso.ofComponents (fun U ↦ comparison.iso (A := A) U)
    (fun f ↦ comparison.naturality (A := A) f)

/-- The component of the normalized-cochain comparison is the objectwise comparison isomorphism. -/
@[simp, stacks 019I "normalized cochain comparison natural isomorphism component"]
theorem comparison.natIso.app (U : CosimplicialObject A) :
    (comparison.natIso (A := A)).app U = comparison.iso U := sorry

end normalizedCochainComplex

end CategoryTheory.CosimplicialObject
