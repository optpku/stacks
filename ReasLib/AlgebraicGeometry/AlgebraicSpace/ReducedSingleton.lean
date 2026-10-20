module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced

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

/-- For an algebraic space `Z` over a scheme `S`, the following are equivalent: `Z` is reduced, locally Noetherian, and
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

namespace ReducedSingleton

/-- An algebraic space is reduced, locally Noetherian, and a singleton on points
if and only if it admits a locally finitely presented, surjective, flat morphism
from the spectrum of a field. -/
theorem iff_exists_field_cover
    {S : Scheme.{u}} {Z : AlgebraicSpace S} :
    IsReduced Z ∧ IsLocallyNoetherian Z ∧ Nonempty (Points Z) ∧
        Subsingleton (Points Z) ↔
      existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z :=
  (isReduced_isLocallyNoetherian_subsingleton_points_tfae Z).out 0 1

/-- `existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z` is equivalent to
the existence of a field-valued point whose morphism is locally of finite
presentation, surjective, and flat. -/
theorem exists_field_cover_iff_fieldValuedPoint
    {S : Scheme.{u}} (Z : AlgebraicSpace S) :
    existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z ↔
      ∃ p : FieldValuedPoint Z,
        LocallyOfFinitePresentation p.hom ∧ Surjective p.hom ∧ Flat p.hom := by
  constructor
  · rintro ⟨k, field, σ, f, hf⟩
    exact ⟨FieldValuedPoint.of k σ f, hf⟩
  · rintro ⟨p, hp⟩
    exact ⟨p.K, p.field, p.structureHom, p.hom, hp⟩

end ReducedSingleton

end AlgebraicGeometry.AlgebraicSpace
