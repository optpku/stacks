/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Lemma_67_48_6_Reduced

/-!
# Reduced singleton algebraic spaces

An algebraic space over a scheme is reduced with a singleton space of points if
and only if it admits a surjective flat morphism from the spectrum of a field,
and if and only if it admits such a morphism that is moreover locally of finite
type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- There exists a field `k` and a surjective flat morphism
`ofOver (Over.mk σ) ⟶ Z` from `Spec (.of k)`. -/
def existsSurjectiveFlatSpecField {S : Scheme.{u}} (Z : AlgebraicSpace S) : Prop :=
  ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S) (f : ofOver (Over.mk σ) ⟶ Z),
    Surjective f ∧ Flat f

namespace existsSurjectiveFlatSpecField

/-- `existsSurjectiveFlatSpecField Z` unpacks to a field `k` and a surjective
flat morphism from `Spec (.of k)` to `Z` over `S`. -/
theorem iff {S : Scheme.{u}} {Z : AlgebraicSpace S} :
    existsSurjectiveFlatSpecField Z ↔
      ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S)
        (f : ofOver (Over.mk σ) ⟶ Z), Surjective f ∧ Flat f :=
  sorry

/-- A surjective flat morphism from `Spec (.of k)` witnesses
`existsSurjectiveFlatSpecField`. -/
theorem of {S : Scheme.{u}} {Z : AlgebraicSpace S} {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S} (f : ofOver (Over.mk σ) ⟶ Z) [Surjective f] [Flat f] :
    existsSurjectiveFlatSpecField Z :=
  sorry

/-- `existsSurjectiveFlatSpecField Z` supplies a field `k` and a surjective
flat morphism from `Spec (.of k)` to `Z`. -/
theorem spec {S : Scheme.{u}} {Z : AlgebraicSpace S}
    (h : existsSurjectiveFlatSpecField Z) :
    ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S)
      (f : ofOver (Over.mk σ) ⟶ Z), Surjective f ∧ Flat f :=
  sorry

end existsSurjectiveFlatSpecField

/-- There exists a field `k` and a locally of finite type, surjective, flat
morphism `ofOver (Over.mk σ) ⟶ Z` from `Spec (.of k)`. -/
def existsLocallyOfFiniteTypeSurjectiveFlatSpecField {S : Scheme.{u}}
    (Z : AlgebraicSpace S) : Prop :=
  ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S) (f : ofOver (Over.mk σ) ⟶ Z),
    LocallyOfFiniteType f ∧ Surjective f ∧ Flat f

namespace existsLocallyOfFiniteTypeSurjectiveFlatSpecField

/-- `existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z` unpacks to a field `k`
and a locally of finite type, surjective, flat morphism from `Spec (.of k)` to
`Z` over `S`. -/
theorem iff {S : Scheme.{u}} {Z : AlgebraicSpace S} :
    existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z ↔
      ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S)
        (f : ofOver (Over.mk σ) ⟶ Z),
        LocallyOfFiniteType f ∧ Surjective f ∧ Flat f :=
  sorry

/-- A locally of finite type, surjective, flat morphism from `Spec (.of k)`
witnesses `existsLocallyOfFiniteTypeSurjectiveFlatSpecField`. -/
theorem of {S : Scheme.{u}} {Z : AlgebraicSpace S} {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S} (f : ofOver (Over.mk σ) ⟶ Z) [LocallyOfFiniteType f]
    [Surjective f] [Flat f] : existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z :=
  sorry

/-- `existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z` supplies a field `k`
and a locally of finite type, surjective, flat morphism from `Spec (.of k)` to
`Z`. -/
theorem spec {S : Scheme.{u}} {Z : AlgebraicSpace S}
    (h : existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z) :
    ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S)
      (f : ofOver (Over.mk σ) ⟶ Z),
      LocallyOfFiniteType f ∧ Surjective f ∧ Flat f :=
  sorry

end existsLocallyOfFiniteTypeSurjectiveFlatSpecField

/-- Lemma 68.13.2: Let `S` be a scheme. Let `Z` be an algebraic space over `S`.
The following are equivalent: `Z` is reduced and `Points Z` is a singleton;
there exists a surjective flat morphism `ofOver (Over.mk σ) ⟶ Z` from
`Spec (.of k)` where `k` is a field; and there exists a locally of finite type,
surjective, flat morphism `ofOver (Over.mk σ) ⟶ Z` from `Spec (.of k)` where
`k` is a field. -/
@[stacks 06QW]
theorem isReduced_subsingleton_points_tfae {S : Scheme.{u}} (Z : AlgebraicSpace S) :
    List.TFAE
      [ IsReduced Z ∧ Nonempty (Points Z) ∧ Subsingleton (Points Z)
      , existsSurjectiveFlatSpecField Z
      , existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z ] :=
  sorry

/-- An algebraic space is reduced with singleton `Points` if and only if it
admits a surjective flat morphism from the spectrum of a field. -/
theorem isReduced_subsingleton_points_iff_existsSurjectiveFlatSpecField
    {S : Scheme.{u}} {Z : AlgebraicSpace S} :
    IsReduced Z ∧ Nonempty (Points Z) ∧ Subsingleton (Points Z) ↔
      existsSurjectiveFlatSpecField Z :=
  sorry

/-- An algebraic space is reduced with singleton `Points` if and only if it
admits a locally of finite type, surjective, flat morphism from the spectrum of
a field. -/
theorem isReduced_subsingleton_points_iff_existsLocallyOfFiniteTypeSurjectiveFlatSpecField
    {S : Scheme.{u}} {Z : AlgebraicSpace S} :
    IsReduced Z ∧ Nonempty (Points Z) ∧ Subsingleton (Points Z) ↔
      existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z :=
  sorry

/-- An algebraic space admits a surjective flat morphism from the spectrum of a
field if and only if it admits one that is moreover locally of finite type. -/
theorem existsSurjectiveFlatSpecField_iff_existsLocallyOfFiniteTypeSurjectiveFlatSpecField
    {S : Scheme.{u}} {Z : AlgebraicSpace S} :
    existsSurjectiveFlatSpecField Z ↔
      existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z :=
  sorry

/-- A reduced algebraic space whose space of points is a singleton admits a
surjective flat morphism from the spectrum of a field. -/
theorem existsSurjectiveFlatSpecField_of_isReduced_subsingleton {S : Scheme.{u}}
    (Z : AlgebraicSpace S) [IsReduced Z] [Nonempty (Points Z)]
    [Subsingleton (Points Z)] : existsSurjectiveFlatSpecField Z :=
  sorry

/-- An algebraic space admitting a surjective flat morphism from the spectrum of
a field is reduced. -/
theorem isReduced_of_existsSurjectiveFlatSpecField {S : Scheme.{u}}
    {Z : AlgebraicSpace S} (h : existsSurjectiveFlatSpecField Z) : IsReduced Z :=
  sorry

/-- An algebraic space admitting a surjective flat morphism from the spectrum of
a field has nonempty `Points`. -/
theorem nonempty_points_of_existsSurjectiveFlatSpecField {S : Scheme.{u}}
    {Z : AlgebraicSpace S} (h : existsSurjectiveFlatSpecField Z) :
    Nonempty (Points Z) :=
  sorry

/-- An algebraic space admitting a surjective flat morphism from the spectrum of
a field has subsingleton `Points`. -/
theorem subsingleton_points_of_existsSurjectiveFlatSpecField {S : Scheme.{u}}
    {Z : AlgebraicSpace S} (h : existsSurjectiveFlatSpecField Z) :
    Subsingleton (Points Z) :=
  sorry

/-- `existsSurjectiveFlatSpecField Z` is equivalent to the existence of a
field-valued point whose morphism is surjective and flat. -/
theorem existsSurjectiveFlatSpecField_iff_fieldValuedPoint {S : Scheme.{u}}
    (Z : AlgebraicSpace S) :
    existsSurjectiveFlatSpecField Z ↔
      ∃ p : FieldValuedPoint Z, Surjective p.hom ∧ Flat p.hom :=
  sorry

/-- `existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z` is equivalent to the
existence of a field-valued point whose morphism is locally of finite type,
surjective, and flat. -/
theorem existsLocallyOfFiniteTypeSurjectiveFlatSpecField_iff_fieldValuedPoint
    {S : Scheme.{u}} (Z : AlgebraicSpace S) :
    existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z ↔
      ∃ p : FieldValuedPoint Z,
        LocallyOfFiniteType p.hom ∧ Surjective p.hom ∧ Flat p.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
