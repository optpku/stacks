module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduced.Singleton

import StacksCheckRecall

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

#check (AlgebraicGeometry.AlgebraicStack.existsSurjectiveFlatSpecField :
  ∀ {S : Scheme.{u}} (Z : GroupoidsOver S)
    [AlgebraicStack Z],
    Prop)

namespace existsSurjectiveFlatSpecField

#check (AlgebraicGeometry.AlgebraicStack.existsSurjectiveFlatSpecField.iff :
  ∀ {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z],
    existsSurjectiveFlatSpecField Z ↔
      ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S)
        (f : GroupoidsOver.slice (Over.mk σ) ⟶ Z),
        Groupoids.Hom.Surjective f ∧ Groupoids.Hom.Flat f)

#check (AlgebraicGeometry.AlgebraicStack.existsSurjectiveFlatSpecField.of :
  ∀ {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z]
    {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : GroupoidsOver.slice (Over.mk σ) ⟶ Z) [Groupoids.Hom.Surjective f]
    [Groupoids.Hom.Flat f],
    existsSurjectiveFlatSpecField Z)

#check (AlgebraicGeometry.AlgebraicStack.existsSurjectiveFlatSpecField.spec :
  ∀ {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z]
    (h : existsSurjectiveFlatSpecField Z),
    ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S)
      (f : GroupoidsOver.slice (Over.mk σ) ⟶ Z),
      Groupoids.Hom.Surjective f ∧ Groupoids.Hom.Flat f)

end existsSurjectiveFlatSpecField

#check (AlgebraicGeometry.AlgebraicStack.existsLocallyOfFiniteTypeSurjectiveFlatSpecField :
  ∀ {S : Scheme.{u}}
    (Z : GroupoidsOver S) [AlgebraicStack Z],
    Prop)

namespace existsLocallyOfFiniteTypeSurjectiveFlatSpecField

#check (AlgebraicGeometry.AlgebraicStack.existsLocallyOfFiniteTypeSurjectiveFlatSpecField.iff :
  ∀ {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z],
    existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z ↔
      ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S)
        (f : GroupoidsOver.slice (Over.mk σ) ⟶ Z),
        Groupoids.Hom.LocallyOfFiniteType f ∧ Groupoids.Hom.Surjective f ∧
          Groupoids.Hom.Flat f)

#check (AlgebraicGeometry.AlgebraicStack.existsLocallyOfFiniteTypeSurjectiveFlatSpecField.of :
  ∀ {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z]
    {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : GroupoidsOver.slice (Over.mk σ) ⟶ Z)
    [Groupoids.Hom.LocallyOfFiniteType f] [Groupoids.Hom.Surjective f]
    [Groupoids.Hom.Flat f],
    existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z)

#check (AlgebraicGeometry.AlgebraicStack.existsLocallyOfFiniteTypeSurjectiveFlatSpecField.spec :
  ∀ {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z]
    (h : existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z),
    ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S)
      (f : GroupoidsOver.slice (Over.mk σ) ⟶ Z),
      Groupoids.Hom.LocallyOfFiniteType f ∧ Groupoids.Hom.Surjective f ∧
        Groupoids.Hom.Flat f)

end existsLocallyOfFiniteTypeSurjectiveFlatSpecField

/- Lemma 100.11.2: An algebraic stack is reduced with exactly one point if and
only if it admits a surjective flat field-spectrum cover, equivalently one that
is locally of finite type. -/
@[stacks 06MN] #check (AlgebraicGeometry.AlgebraicStack.isReduced_subsingleton_points_tfae :
  ∀ {S : Scheme.{u}} (Z : GroupoidsOver S)
    [AlgebraicStack Z],
    List.TFAE
      [ IsReduced Z ∧ Nonempty (Points Z) ∧ Subsingleton (Points Z)
      , existsSurjectiveFlatSpecField Z
      , existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z ])

#check (AlgebraicGeometry.AlgebraicStack.isReduced_subsingleton_points_iff_existsSurjectiveFlatSpecField :
  ∀ {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z],
    IsReduced Z ∧ Nonempty (Points Z) ∧ Subsingleton (Points Z) ↔
      existsSurjectiveFlatSpecField Z)

#check (AlgebraicGeometry.AlgebraicStack.ReducedSingleton.iff_locallyOfFiniteType_fieldCover :
  ∀ {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z],
    IsReduced Z ∧ Nonempty (Points Z) ∧ Subsingleton (Points Z) ↔
      existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z)

#check (AlgebraicGeometry.AlgebraicStack.ReducedSingleton.fieldCover_iff_locallyOfFiniteType :
  ∀ {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z],
    existsSurjectiveFlatSpecField Z ↔
      existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z)

#check (AlgebraicGeometry.AlgebraicStack.existsSurjectiveFlatSpecField_of_isReduced_subsingleton :
  ∀ {S : Scheme.{u}}
    (Z : GroupoidsOver S) [AlgebraicStack Z] [IsReduced Z] [Nonempty (Points Z)]
    [Subsingleton (Points Z)],
    existsSurjectiveFlatSpecField Z)

#check (AlgebraicGeometry.AlgebraicStack.isReduced_of_existsSurjectiveFlatSpecField :
  ∀ {S : Scheme.{u}}
    {Z : GroupoidsOver S} [AlgebraicStack Z]
    (h : existsSurjectiveFlatSpecField Z),
    IsReduced Z)

#check (AlgebraicGeometry.AlgebraicStack.nonempty_points_of_existsSurjectiveFlatSpecField :
  ∀ {S : Scheme.{u}}
    {Z : GroupoidsOver S} [AlgebraicStack Z]
    (h : existsSurjectiveFlatSpecField Z),
    Nonempty (Points Z))

#check (AlgebraicGeometry.AlgebraicStack.subsingleton_points_of_existsSurjectiveFlatSpecField :
  ∀ {S : Scheme.{u}}
    {Z : GroupoidsOver S} [AlgebraicStack Z]
    (h : existsSurjectiveFlatSpecField Z),
    Subsingleton (Points Z))

#check (AlgebraicGeometry.AlgebraicStack.existsSurjectiveFlatSpecField_iff_fieldValuedPoint :
  ∀ {S : Scheme.{u}}
    (Z : GroupoidsOver S) [AlgebraicStack Z],
    existsSurjectiveFlatSpecField Z ↔
      ∃ p : FieldValuedPoint Z,
        Groupoids.Hom.Surjective p.hom ∧ Groupoids.Hom.Flat p.hom)

#check (AlgebraicGeometry.AlgebraicStack.existsLocallyOfFiniteTypeSurjectiveFlatSpecField_iff_fieldValuedPoint :
  ∀ {S : Scheme.{u}} (Z : GroupoidsOver S) [AlgebraicStack Z],
    existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z ↔
      ∃ p : FieldValuedPoint Z,
        Groupoids.Hom.LocallyOfFiniteType p.hom ∧ Groupoids.Hom.Surjective p.hom ∧
          Groupoids.Hom.Flat p.hom)

end AlgebraicGeometry.AlgebraicStack
