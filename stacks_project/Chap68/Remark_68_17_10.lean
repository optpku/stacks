/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap68.Remark_68_17_10_Relative
public import stacks_project.Chap68.Remark_68_17_10_VeryReasonable

/-!
# Fibres of relative conditions

A morphism of algebraic spaces has a relative object-level condition such as (β),
decent, reasonable, or very reasonable when, loosely speaking, its fibres have that
property. The precise test is scheme-base-change of the source; field-valued fibres
are the informal special case.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Remark 68.17.10: a morphism of algebraic spaces is relatively (β), decent,
reasonable, or very reasonable when, loosely speaking, its fibres have the
corresponding object-level property from Section 68.6. Precisely, if `f` is
relatively `P` in the sense of scheme-base-changes of the source, then every
field-valued fibre of `f` has `P`. Being decent is useful for specializations of
points on `|X|`; being reasonable is stronger and technically easier. -/
@[stacks 03L4]
theorem isRelatively_fieldValuedFibre {S : Scheme.{u}}
    {P : ObjectProperty (AlgebraicSpace S)} {X Y W : AlgebraicSpace S}
    {f : X ⟶ Y} (y : FieldValuedPoint Y)
    {pY : W ⟶ ofOver (Over.mk y.structureHom)} {pX : W ⟶ X}
    [IsRelatively P f] (h : IsPullback pY pX y.hom f) : P W := sorry

/-- If `f` has property (β), then every field-valued fibre of `f` has property (β). -/
theorem propertyBeta_fieldValuedFibre {S : Scheme.{u}} {X Y W : AlgebraicSpace S}
    {f : X ⟶ Y} (y : FieldValuedPoint Y)
    {pY : W ⟶ ofOver (Over.mk y.structureHom)} {pX : W ⟶ X}
    [PropertyBeta f] (h : IsPullback pY pX y.hom f) :
    HasPropertyBeta W := sorry

/-- If `f` is a decent morphism, then every field-valued fibre of `f` is a decent
algebraic space. -/
theorem isDecent_fieldValuedFibre {S : Scheme.{u}} {X Y W : AlgebraicSpace S}
    {f : X ⟶ Y} (y : FieldValuedPoint Y)
    {pY : W ⟶ ofOver (Over.mk y.structureHom)} {pX : W ⟶ X}
    [Decent f] (h : IsPullback pY pX y.hom f) :
    IsDecent W := sorry

/-- If `f` is a reasonable morphism, then every field-valued fibre of `f` is a
reasonable algebraic space. -/
theorem reasonable_fieldValuedFibre {S : Scheme.{u}} {X Y W : AlgebraicSpace S}
    {f : X ⟶ Y} (y : FieldValuedPoint Y)
    {pY : W ⟶ ofOver (Over.mk y.structureHom)} {pX : W ⟶ X}
    [Reasonable f] (h : IsPullback pY pX y.hom f) :
    IsReasonable W := sorry

/-- A very reasonable morphism, in the fourth sense of Definition 68.17.1, has
very reasonable field-valued fibres, retaining all four properties of Remark 68.17.10. -/
theorem veryReasonable_fieldValuedFibre {S : Scheme.{u}} {X Y W : AlgebraicSpace S}
    {f : X ⟶ Y} (y : FieldValuedPoint Y)
    {pY : W ⟶ ofOver (Over.mk y.structureHom)} {pX : W ⟶ X}
    [VeryReasonable f] (h : IsPullback pY pX y.hom f) :
    IsVeryReasonable W := VeryReasonable.ofOver_isPullback h

end AlgebraicGeometry.AlgebraicSpace
