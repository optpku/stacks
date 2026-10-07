module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap100.Lemma_100_11_1_Flat
public import stacks_project.Chap100.Lemma_100_11_2_Reduced
public import stacks_project.Chap100.Lemma_100_11_3_LocallyNoetherian

/-!
# Reduced locally Noetherian singleton algebraic stacks

An algebraic stack over a scheme is reduced, locally Noetherian, and a
singleton on points if and only if it admits a locally finitely presented,
surjective, flat morphism from the spectrum of a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- There exists a field `k` and a locally finitely presented, surjective, flat
morphism `GroupoidsOver.slice (Over.mk σ) ⟶ Z` from `Spec (.of k)`. -/
def existsLocallyOfFinitePresentationSurjectiveFlatSpecField {S : Scheme.{u}}
    (Z : GroupoidsOver S) [AlgebraicStack Z] : Prop :=
  ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S)
    (f : GroupoidsOver.slice (Over.mk σ) ⟶ Z),
    Groupoids.Hom.LocallyOfFinitePresentation f ∧ Groupoids.Hom.Surjective f ∧
      Groupoids.Hom.Flat f

/-- `existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z` unpacks to a
field `k` and a locally finitely presented, surjective, flat morphism from
`Spec (.of k)` to `Z` over `S`. -/
theorem existsLocallyOfFinitePresentationSurjectiveFlatSpecField_iff
    {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z] :
    existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z ↔
      ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S)
        (f : GroupoidsOver.slice (Over.mk σ) ⟶ Z),
        Groupoids.Hom.LocallyOfFinitePresentation f ∧
          Groupoids.Hom.Surjective f ∧ Groupoids.Hom.Flat f :=
  sorry

/-- A locally finitely presented, surjective, flat morphism from `Spec (.of k)`
witnesses `existsLocallyOfFinitePresentationSurjectiveFlatSpecField`. -/
theorem existsLocallyOfFinitePresentationSurjectiveFlatSpecField_of
    {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z]
    {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : GroupoidsOver.slice (Over.mk σ) ⟶ Z)
    [Groupoids.Hom.LocallyOfFinitePresentation f] [Groupoids.Hom.Surjective f]
    [Groupoids.Hom.Flat f] :
    existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z :=
  sorry

/-- `existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z` supplies a
field `k` and a locally finitely presented, surjective, flat morphism from
`Spec (.of k)` to `Z`. -/
theorem existsLocallyOfFinitePresentationSurjectiveFlatSpecField_spec
    {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z]
    (h : existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z) :
    ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S)
      (f : GroupoidsOver.slice (Over.mk σ) ⟶ Z),
      Groupoids.Hom.LocallyOfFinitePresentation f ∧
        Groupoids.Hom.Surjective f ∧ Groupoids.Hom.Flat f :=
  sorry

/-- Lemma 100.11.3: Let `Z` be an algebraic stack. The following are equivalent:
`Z` is reduced, locally Noetherian, and `|Z|` is a singleton; and there exists
a locally finitely presented, surjective, flat morphism `Spec (.of k) ⟶ Z`
where `k` is a field. -/
@[stacks 06MP]
theorem isReduced_isLocallyNoetherian_subsingleton_points_tfae {S : Scheme.{u}}
    (Z : GroupoidsOver S) [AlgebraicStack Z] :
    List.TFAE
      [ IsReduced Z ∧ IsLocallyNoetherian Z ∧ Nonempty (Points Z) ∧
          Subsingleton (Points Z)
      , existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z ] :=
  sorry

/-- An algebraic stack is reduced, locally Noetherian, and a singleton on points
if and only if it admits a locally finitely presented, surjective, flat
morphism from the spectrum of a field. -/
theorem isReduced_isLocallyNoetherian_subsingleton_points_iff_existsLocallyOfFinitePresentationSurjectiveFlatSpecField
    {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z] :
    IsReduced Z ∧ IsLocallyNoetherian Z ∧ Nonempty (Points Z) ∧
        Subsingleton (Points Z) ↔
      existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z :=
  sorry

/-- A reduced, locally Noetherian algebraic stack whose space of points is a
singleton admits a locally finitely presented, surjective, flat morphism from
the spectrum of a field. -/
theorem existsLocallyOfFinitePresentationSurjectiveFlatSpecField_of_isReduced_isLocallyNoetherian_subsingleton
    {S : Scheme.{u}} (Z : GroupoidsOver S) [AlgebraicStack Z] [IsReduced Z]
    [IsLocallyNoetherian Z] [Nonempty (Points Z)] [Subsingleton (Points Z)] :
    existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z :=
  sorry

/-- An algebraic stack admitting a locally finitely presented, surjective, flat
morphism from the spectrum of a field is reduced. -/
theorem isReduced_of_existsLocallyOfFinitePresentationSurjectiveFlatSpecField
    {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z]
    (h : existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z) :
    IsReduced Z :=
  sorry

/-- An algebraic stack admitting a locally finitely presented, surjective, flat
morphism from the spectrum of a field is locally Noetherian. -/
theorem isLocallyNoetherian_of_existsLocallyOfFinitePresentationSurjectiveFlatSpecField
    {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z]
    (h : existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z) :
    IsLocallyNoetherian Z :=
  sorry

/-- An algebraic stack admitting a locally finitely presented, surjective, flat
morphism from the spectrum of a field has nonempty `Points`. -/
theorem nonempty_points_of_existsLocallyOfFinitePresentationSurjectiveFlatSpecField
    {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z]
    (h : existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z) :
    Nonempty (Points Z) :=
  sorry

/-- An algebraic stack admitting a locally finitely presented, surjective, flat
morphism from the spectrum of a field has subsingleton `Points`. -/
theorem subsingleton_points_of_existsLocallyOfFinitePresentationSurjectiveFlatSpecField
    {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z]
    (h : existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z) :
    Subsingleton (Points Z) :=
  sorry

/-- `existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z` is equivalent
to the existence of a field-valued point whose morphism is locally of finite
presentation, surjective, and flat. -/
theorem existsLocallyOfFinitePresentationSurjectiveFlatSpecField_iff_fieldValuedPoint
    {S : Scheme.{u}} (Z : GroupoidsOver S) [AlgebraicStack Z] :
    existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z ↔
      ∃ p : FieldValuedPoint Z,
        Groupoids.Hom.LocallyOfFinitePresentation p.hom ∧
          Groupoids.Hom.Surjective p.hom ∧ Groupoids.Hom.Flat p.hom :=
  sorry

end AlgebraicGeometry.AlgebraicStack
