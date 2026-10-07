module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Lemma_67_48_6_Reduced

/-!
# Reduced locally Noetherian singleton algebraic spaces

An algebraic space over a scheme is reduced, locally Noetherian, and a singleton
on points if and only if it admits a locally finitely presented, surjective,
flat morphism from the spectrum of a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- There exists a field `k` and a locally finitely presented, surjective, flat
morphism `ofOver (Over.mk σ) ⟶ Z` from `Spec (.of k)`. -/
def existsLocallyOfFinitePresentationSurjectiveFlatSpecField {S : Scheme.{u}}
    (Z : AlgebraicSpace S) : Prop :=
  ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S) (f : ofOver (Over.mk σ) ⟶ Z),
    LocallyOfFinitePresentation f ∧ Surjective f ∧ Flat f

/-- `existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z` unpacks to a
field `k` and a locally finitely presented, surjective, flat morphism from
`Spec (.of k)` to `Z` over `S`. -/
theorem existsLocallyOfFinitePresentationSurjectiveFlatSpecField_iff
    {S : Scheme.{u}} {Z : AlgebraicSpace S} :
    existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z ↔
      ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S)
        (f : ofOver (Over.mk σ) ⟶ Z),
        LocallyOfFinitePresentation f ∧ Surjective f ∧ Flat f :=
  sorry

/-- A locally finitely presented, surjective, flat morphism from `Spec (.of k)`
witnesses `existsLocallyOfFinitePresentationSurjectiveFlatSpecField`. -/
theorem existsLocallyOfFinitePresentationSurjectiveFlatSpecField_of
    {S : Scheme.{u}} {Z : AlgebraicSpace S} {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S} (f : ofOver (Over.mk σ) ⟶ Z)
    [LocallyOfFinitePresentation f] [Surjective f] [Flat f] :
    existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z :=
  sorry

/-- `existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z` supplies a field
`k` and a locally finitely presented, surjective, flat morphism from
`Spec (.of k)` to `Z`. -/
theorem existsLocallyOfFinitePresentationSurjectiveFlatSpecField_spec
    {S : Scheme.{u}} {Z : AlgebraicSpace S}
    (h : existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z) :
    ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S)
      (f : ofOver (Over.mk σ) ⟶ Z),
      LocallyOfFinitePresentation f ∧ Surjective f ∧ Flat f :=
  sorry

/-- Lemma 68.13.3: Let `S` be a scheme. Let `Z` be an algebraic space over `S`.
The following are equivalent: `Z` is reduced, locally Noetherian, and
`Points Z` is a singleton; and there exists a locally finitely presented,
surjective, flat morphism `ofOver (Over.mk σ) ⟶ Z` from `Spec (.of k)` where
`k` is a field. -/
@[stacks 06QX]
theorem isReduced_isLocallyNoetherian_subsingleton_points_tfae
    {S : Scheme.{u}} (Z : AlgebraicSpace S) :
    List.TFAE
      [ IsReduced Z ∧ IsLocallyNoetherian Z ∧ Nonempty (Points Z) ∧
          Subsingleton (Points Z)
      , existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z ] :=
  sorry

/-- An algebraic space is reduced, locally Noetherian, and a singleton on points
if and only if it admits a locally finitely presented, surjective, flat morphism
from the spectrum of a field. -/
theorem isReduced_isLocallyNoetherian_subsingleton_points_iff_existsLocallyOfFinitePresentationSurjectiveFlatSpecField
    {S : Scheme.{u}} {Z : AlgebraicSpace S} :
    IsReduced Z ∧ IsLocallyNoetherian Z ∧ Nonempty (Points Z) ∧
        Subsingleton (Points Z) ↔
      existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z :=
  sorry

/-- A reduced, locally Noetherian algebraic space whose space of points is a
singleton admits a locally finitely presented, surjective, flat morphism from
the spectrum of a field. -/
theorem existsLocallyOfFinitePresentationSurjectiveFlatSpecField_of_isReduced_isLocallyNoetherian_subsingleton
    {S : Scheme.{u}} (Z : AlgebraicSpace S) [IsReduced Z]
    [IsLocallyNoetherian Z] [Nonempty (Points Z)] [Subsingleton (Points Z)] :
    existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z :=
  sorry

/-- An algebraic space admitting a locally finitely presented, surjective, flat
morphism from the spectrum of a field is reduced. -/
theorem isReduced_of_existsLocallyOfFinitePresentationSurjectiveFlatSpecField
    {S : Scheme.{u}} {Z : AlgebraicSpace S}
    (h : existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z) :
    IsReduced Z :=
  sorry

/-- An algebraic space admitting a locally finitely presented, surjective, flat
morphism from the spectrum of a field is locally Noetherian. -/
theorem isLocallyNoetherian_of_existsLocallyOfFinitePresentationSurjectiveFlatSpecField
    {S : Scheme.{u}} {Z : AlgebraicSpace S}
    (h : existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z) :
    IsLocallyNoetherian Z :=
  sorry

/-- An algebraic space admitting a locally finitely presented, surjective, flat
morphism from the spectrum of a field has nonempty `Points`. -/
theorem nonempty_points_of_existsLocallyOfFinitePresentationSurjectiveFlatSpecField
    {S : Scheme.{u}} {Z : AlgebraicSpace S}
    (h : existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z) :
    Nonempty (Points Z) :=
  sorry

/-- An algebraic space admitting a locally finitely presented, surjective, flat
morphism from the spectrum of a field has subsingleton `Points`. -/
theorem subsingleton_points_of_existsLocallyOfFinitePresentationSurjectiveFlatSpecField
    {S : Scheme.{u}} {Z : AlgebraicSpace S}
    (h : existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z) :
    Subsingleton (Points Z) :=
  sorry

/-- `existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z` is equivalent to
the existence of a field-valued point whose morphism is locally of finite
presentation, surjective, and flat. -/
theorem existsLocallyOfFinitePresentationSurjectiveFlatSpecField_iff_fieldValuedPoint
    {S : Scheme.{u}} (Z : AlgebraicSpace S) :
    existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z ↔
      ∃ p : FieldValuedPoint Z,
        LocallyOfFinitePresentation p.hom ∧ Surjective p.hom ∧ Flat p.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
