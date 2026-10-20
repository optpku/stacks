module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldCover
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced

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
  Iff.rfl

/-- A surjective flat morphism from `Spec (.of k)` witnesses
`existsSurjectiveFlatSpecField`. -/
theorem of {S : Scheme.{u}} {Z : AlgebraicSpace S} {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S} (f : ofOver (Over.mk σ) ⟶ Z) [Surjective f] [Flat f] :
    existsSurjectiveFlatSpecField Z :=
  ⟨k, inferInstance, σ, f, inferInstance, inferInstance⟩

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
  Iff.rfl

/-- A locally of finite type, surjective, flat morphism from `Spec (.of k)`
witnesses `existsLocallyOfFiniteTypeSurjectiveFlatSpecField`. -/
theorem of {S : Scheme.{u}} {Z : AlgebraicSpace S} {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S} (f : ofOver (Over.mk σ) ⟶ Z) [LocallyOfFiniteType f]
    [Surjective f] [Flat f] : existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z :=
  ⟨k, inferInstance, σ, f, inferInstance, inferInstance, inferInstance⟩

end existsLocallyOfFiniteTypeSurjectiveFlatSpecField

/-- For an algebraic space `Z` over a scheme `S`,
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
  (isReduced_subsingleton_points_tfae Z).out 0 1

namespace ReducedSingleton

/-- An algebraic space is reduced with singleton `Points` if and only if it
admits a locally of finite type, surjective, flat morphism from the spectrum of
a field. -/
theorem iff_locallyOfFiniteType_fieldCover
    {S : Scheme.{u}} {Z : AlgebraicSpace S} :
    IsReduced Z ∧ Nonempty (Points Z) ∧ Subsingleton (Points Z) ↔
      existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z :=
  (isReduced_subsingleton_points_tfae Z).out 0 2

/-- An algebraic space admits a surjective flat morphism from the spectrum of a
field if and only if it admits one that is moreover locally of finite type. -/
theorem fieldCover_iff_locallyOfFiniteType
    {S : Scheme.{u}} {Z : AlgebraicSpace S} :
    existsSurjectiveFlatSpecField Z ↔
      existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z :=
  (isReduced_subsingleton_points_tfae Z).out 1 2

end ReducedSingleton

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
