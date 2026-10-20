module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduced
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat

/-!
# Reduced singleton algebraic stacks

An algebraic stack over a scheme is reduced with a singleton space of points if
and only if it admits a surjective flat morphism from the spectrum of a field,
and if and only if it admits such a morphism that is moreover locally of finite
type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- There exists a field `k` and a surjective flat morphism
`GroupoidsOver.slice (Over.mk σ) ⟶ Z` from `Spec (.of k)`. -/
def existsSurjectiveFlatSpecField {S : Scheme.{u}} (Z : GroupoidsOver S)
    [AlgebraicStack Z] : Prop :=
  ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S)
    (f : GroupoidsOver.slice (Over.mk σ) ⟶ Z),
    Groupoids.Hom.Surjective f ∧ Groupoids.Hom.Flat f

namespace existsSurjectiveFlatSpecField

/-- `existsSurjectiveFlatSpecField Z` unpacks to a field `k` and a surjective
flat morphism from `Spec (.of k)` to `Z` over `S`. -/
theorem iff {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z] :
    existsSurjectiveFlatSpecField Z ↔
      ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S)
        (f : GroupoidsOver.slice (Over.mk σ) ⟶ Z),
        Groupoids.Hom.Surjective f ∧ Groupoids.Hom.Flat f :=
  sorry

/-- A surjective flat morphism from `Spec (.of k)` witnesses
`existsSurjectiveFlatSpecField`. -/
theorem of {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z]
    {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : GroupoidsOver.slice (Over.mk σ) ⟶ Z) [Groupoids.Hom.Surjective f]
    [Groupoids.Hom.Flat f] : existsSurjectiveFlatSpecField Z :=
  sorry

/-- `existsSurjectiveFlatSpecField Z` supplies a field `k` and a surjective
flat morphism from `Spec (.of k)` to `Z`. -/
theorem spec {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z]
    (h : existsSurjectiveFlatSpecField Z) :
    ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S)
      (f : GroupoidsOver.slice (Over.mk σ) ⟶ Z),
      Groupoids.Hom.Surjective f ∧ Groupoids.Hom.Flat f :=
  sorry

end existsSurjectiveFlatSpecField

/-- There exists a field `k` and a locally of finite type, surjective, flat
morphism `GroupoidsOver.slice (Over.mk σ) ⟶ Z` from `Spec (.of k)`. -/
def existsLocallyOfFiniteTypeSurjectiveFlatSpecField {S : Scheme.{u}}
    (Z : GroupoidsOver S) [AlgebraicStack Z] : Prop :=
  ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S)
    (f : GroupoidsOver.slice (Over.mk σ) ⟶ Z),
    Groupoids.Hom.LocallyOfFiniteType f ∧ Groupoids.Hom.Surjective f ∧
      Groupoids.Hom.Flat f

namespace existsLocallyOfFiniteTypeSurjectiveFlatSpecField

/-- `existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z` unpacks to a field `k`
and a locally of finite type, surjective, flat morphism from `Spec (.of k)` to
`Z` over `S`. -/
theorem iff {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z] :
    existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z ↔
      ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S)
        (f : GroupoidsOver.slice (Over.mk σ) ⟶ Z),
        Groupoids.Hom.LocallyOfFiniteType f ∧ Groupoids.Hom.Surjective f ∧
          Groupoids.Hom.Flat f :=
  sorry

/-- A locally of finite type, surjective, flat morphism from `Spec (.of k)`
witnesses `existsLocallyOfFiniteTypeSurjectiveFlatSpecField`. -/
theorem of {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z]
    {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : GroupoidsOver.slice (Over.mk σ) ⟶ Z)
    [Groupoids.Hom.LocallyOfFiniteType f] [Groupoids.Hom.Surjective f]
    [Groupoids.Hom.Flat f] :
    existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z :=
  sorry

/-- `existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z` supplies a field `k`
and a locally of finite type, surjective, flat morphism from `Spec (.of k)` to
`Z`. -/
theorem spec {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z]
    (h : existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z) :
    ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S)
      (f : GroupoidsOver.slice (Over.mk σ) ⟶ Z),
      Groupoids.Hom.LocallyOfFiniteType f ∧ Groupoids.Hom.Surjective f ∧
        Groupoids.Hom.Flat f :=
  sorry

end existsLocallyOfFiniteTypeSurjectiveFlatSpecField

/-- For an algebraic stack `Z`, the following are equivalent:
`Z` is reduced and `|Z|` is a singleton; there exists a surjective flat morphism
`Spec (.of k) ⟶ Z` where `k` is a field; and there exists a locally of finite
type, surjective, flat morphism `Spec (.of k) ⟶ Z` where `k` is a field. -/
@[stacks 06MN]
theorem isReduced_subsingleton_points_tfae {S : Scheme.{u}} (Z : GroupoidsOver S)
    [AlgebraicStack Z] :
    List.TFAE
      [ IsReduced Z ∧ Nonempty (Points Z) ∧ Subsingleton (Points Z)
      , existsSurjectiveFlatSpecField Z
      , existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z ] :=
  sorry

/-- An algebraic stack is reduced with singleton `Points` if and only if it
admits a surjective flat morphism from the spectrum of a field. -/
theorem isReduced_subsingleton_points_iff_existsSurjectiveFlatSpecField
    {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z] :
    IsReduced Z ∧ Nonempty (Points Z) ∧ Subsingleton (Points Z) ↔
      existsSurjectiveFlatSpecField Z :=
  sorry

namespace ReducedSingleton

/-- An algebraic stack is reduced with singleton `Points` if and only if it
admits a locally of finite type, surjective, flat morphism from the spectrum of
a field. -/
theorem iff_locallyOfFiniteType_fieldCover
    {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z] :
    IsReduced Z ∧ Nonempty (Points Z) ∧ Subsingleton (Points Z) ↔
      existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z :=
  sorry

/-- An algebraic stack admits a surjective flat morphism from the spectrum of a
field if and only if it admits one that is moreover locally of finite type. -/
theorem fieldCover_iff_locallyOfFiniteType
    {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z] :
    existsSurjectiveFlatSpecField Z ↔
      existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z :=
  sorry

end ReducedSingleton

/-- A reduced algebraic stack whose space of points is a singleton admits a
surjective flat morphism from the spectrum of a field. -/
theorem existsSurjectiveFlatSpecField_of_isReduced_subsingleton {S : Scheme.{u}}
    (Z : GroupoidsOver S) [AlgebraicStack Z] [IsReduced Z] [Nonempty (Points Z)]
    [Subsingleton (Points Z)] : existsSurjectiveFlatSpecField Z :=
  sorry

/-- An algebraic stack admitting a surjective flat morphism from the spectrum of
a field is reduced. -/
theorem isReduced_of_existsSurjectiveFlatSpecField {S : Scheme.{u}}
    {Z : GroupoidsOver S} [AlgebraicStack Z]
    (h : existsSurjectiveFlatSpecField Z) : IsReduced Z :=
  sorry

/-- An algebraic stack admitting a surjective flat morphism from the spectrum of
a field has nonempty `Points`. -/
theorem nonempty_points_of_existsSurjectiveFlatSpecField {S : Scheme.{u}}
    {Z : GroupoidsOver S} [AlgebraicStack Z]
    (h : existsSurjectiveFlatSpecField Z) : Nonempty (Points Z) :=
  sorry

/-- An algebraic stack admitting a surjective flat morphism from the spectrum of
a field has subsingleton `Points`. -/
theorem subsingleton_points_of_existsSurjectiveFlatSpecField {S : Scheme.{u}}
    {Z : GroupoidsOver S} [AlgebraicStack Z]
    (h : existsSurjectiveFlatSpecField Z) : Subsingleton (Points Z) :=
  sorry

/-- `existsSurjectiveFlatSpecField Z` is equivalent to the existence of a
field-valued point whose morphism is surjective and flat. -/
theorem existsSurjectiveFlatSpecField_iff_fieldValuedPoint {S : Scheme.{u}}
    (Z : GroupoidsOver S) [AlgebraicStack Z] :
    existsSurjectiveFlatSpecField Z ↔
      ∃ p : FieldValuedPoint Z,
        Groupoids.Hom.Surjective p.hom ∧ Groupoids.Hom.Flat p.hom :=
  sorry

/-- `existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z` is equivalent to the
existence of a field-valued point whose morphism is locally of finite type,
surjective, and flat. -/
theorem existsLocallyOfFiniteTypeSurjectiveFlatSpecField_iff_fieldValuedPoint
    {S : Scheme.{u}} (Z : GroupoidsOver S) [AlgebraicStack Z] :
    existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z ↔
      ∃ p : FieldValuedPoint Z,
        Groupoids.Hom.LocallyOfFiniteType p.hom ∧ Groupoids.Hom.Surjective p.hom ∧
          Groupoids.Hom.Flat p.hom :=
  sorry

end AlgebraicGeometry.AlgebraicStack
