/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction

/-!
# Representations of self 2-fibre products

An algebraic-space representation of a self 2-fibre product identifies both
projections and the diagonal with the canonical bicategorical morphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic space `R` with projections `s`, `t` and diagonal `e` represents
the self 2-fibre product of a 1-morphism `p : GroupoidsOver.slice U ⟶ X`. -/
def IsSelfFibreProduct {S : Scheme.{u}} {X : GroupoidsOver S} {U : Over S}
    (p : GroupoidsOver.slice U ⟶ X) {R : AlgebraicSpace S}
    (s t : R ⟶ AlgebraicSpace.ofOver U)
    (e : AlgebraicSpace.ofOver U ⟶ R) : Prop :=
  ∃ eqv : TwoFibreProduct.apex.{u + 1, u, u + 1, u} p p ≌ R.toGroupoids,
    Nonempty
        (eqv.hom ≫ AlgebraicSpace.toGroupoids.map s ≫
            (AlgebraicSpace.ofOverSliceEquiv U).hom ≅
          TwoFibreProduct.fst.{u + 1, u, u + 1, u} p p) ∧
      Nonempty
        (eqv.hom ≫ AlgebraicSpace.toGroupoids.map t ≫
            (AlgebraicSpace.ofOverSliceEquiv U).hom ≅
          TwoFibreProduct.snd.{u + 1, u, u + 1, u} p p) ∧
      Nonempty
        ((AlgebraicSpace.ofOverSliceEquiv U).hom ≫
            Hom.diagonal.{u + 1, u, u + 1} p ≫ eqv.hom ≅
          AlgebraicSpace.toGroupoids.map e)

/-- `IsSelfFibreProduct` means there is a bicategorical equivalence of `R` with
the self 2-fibre product of `p` identifying `s`, `t`, and `e` with
`TwoFibreProduct.fst`, `TwoFibreProduct.snd`, and `Hom.diagonal`. -/
theorem isSelfFibreProduct_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Over S} (p : GroupoidsOver.slice U ⟶ X) {R : AlgebraicSpace S}
    (s t : R ⟶ AlgebraicSpace.ofOver U) (e : AlgebraicSpace.ofOver U ⟶ R) :
    IsSelfFibreProduct p s t e ↔
      ∃ eqv : TwoFibreProduct.apex.{u + 1, u, u + 1, u} p p ≌ R.toGroupoids,
        Nonempty
            (eqv.hom ≫ AlgebraicSpace.toGroupoids.map s ≫
                (AlgebraicSpace.ofOverSliceEquiv U).hom ≅
              TwoFibreProduct.fst.{u + 1, u, u + 1, u} p p) ∧
          Nonempty
            (eqv.hom ≫ AlgebraicSpace.toGroupoids.map t ≫
                (AlgebraicSpace.ofOverSliceEquiv U).hom ≅
              TwoFibreProduct.snd.{u + 1, u, u + 1, u} p p) ∧
          Nonempty
            ((AlgebraicSpace.ofOverSliceEquiv U).hom ≫
                Hom.diagonal.{u + 1, u, u + 1} p ≫ eqv.hom ≅
              AlgebraicSpace.toGroupoids.map e) :=
  sorry

/-- `IsSelfFibreProduct` yields the representing base change of `p` along `p`
together with the diagonal section identities for `s` and `t`. -/
theorem isSelfFibreProduct_spec {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Over S} {p : GroupoidsOver.slice U ⟶ X} {R : AlgebraicSpace S}
    {s t : R ⟶ AlgebraicSpace.ofOver U} {e : AlgebraicSpace.ofOver U ⟶ R}
    (hR : IsSelfFibreProduct p s t e) :
    RepresentsBaseChange p p R s ∧
      e ≫ s = 𝟙 (AlgebraicSpace.ofOver U) ∧
      e ≫ t = 𝟙 (AlgebraicSpace.ofOver U) :=
  sorry

namespace IsSelfFibreProduct

/-- A self fibre product representation of `p` yields `RepresentsBaseChange` for
the first projection. -/
theorem representsBaseChange {S : Scheme.{u}} {X : GroupoidsOver S} {U : Over S}
    {p : GroupoidsOver.slice U ⟶ X} {R : AlgebraicSpace S}
    {s t : R ⟶ AlgebraicSpace.ofOver U} {e : AlgebraicSpace.ofOver U ⟶ R}
    (hR : IsSelfFibreProduct p s t e) :
    RepresentsBaseChange p p R s :=
  sorry

/-- The diagonal of a self fibre product is a section of the source projection. -/
theorem source {S : Scheme.{u}} {X : GroupoidsOver S} {U : Over S}
    {p : GroupoidsOver.slice U ⟶ X} {R : AlgebraicSpace S}
    {s t : R ⟶ AlgebraicSpace.ofOver U} {e : AlgebraicSpace.ofOver U ⟶ R}
    (hR : IsSelfFibreProduct p s t e) :
    e ≫ s = 𝟙 (AlgebraicSpace.ofOver U) :=
  sorry

/-- The diagonal of a self fibre product is a section of the target projection. -/
theorem target {S : Scheme.{u}} {X : GroupoidsOver S} {U : Over S}
    {p : GroupoidsOver.slice U ⟶ X} {R : AlgebraicSpace S}
    {s t : R ⟶ AlgebraicSpace.ofOver U} {e : AlgebraicSpace.ofOver U ⟶ R}
    (hR : IsSelfFibreProduct p s t e) :
    e ≫ t = 𝟙 (AlgebraicSpace.ofOver U) :=
  sorry

/-- The algebraic-space diagonal corresponds to `Hom.diagonal p` along the
representing equivalence. -/
theorem diagonal {S : Scheme.{u}} {X : GroupoidsOver S} {U : Over S}
    {p : GroupoidsOver.slice U ⟶ X} {R : AlgebraicSpace S}
    {s t : R ⟶ AlgebraicSpace.ofOver U} {e : AlgebraicSpace.ofOver U ⟶ R}
    (hR : IsSelfFibreProduct p s t e) :
    ∃ eqv : TwoFibreProduct.apex.{u + 1, u, u + 1, u} p p ≌ R.toGroupoids,
      Nonempty
        ((AlgebraicSpace.ofOverSliceEquiv U).hom ≫
            Hom.diagonal.{u + 1, u, u + 1} p ≫ eqv.hom ≅
          AlgebraicSpace.toGroupoids.map e) :=
  sorry

end IsSelfFibreProduct

end AlgebraicGeometry.AlgebraicStack
