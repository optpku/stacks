/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicStack.SmoothPresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SmoothLocal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids.Hom
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property

/-!
# Smooth-local criteria for properties of morphisms of algebraic stacks

Properties of algebraic-space morphisms that are smooth local on source and
target can be tested on smooth presentation squares of algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Every 2-commutative algebraic-space square over `f` with smooth vertical
arrows and smooth comparison into `TwoFibreProduct.apex f b` has `P` on the top
arrow. -/
def forallSmoothComparison {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : GroupoidsOver S}
    (f : X ⟶ Y) : Prop :=
  ∀ {U V : AlgebraicSpace S} (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
    (h : U ⟶ V),
    IsSmoothSpaceSquare f a b h → HasSmoothComparison f a b h → P h

/-- `forallSmoothComparison P f` means `P` holds on the top arrow of every smooth
algebraic-space square over `f` with smooth comparison. -/
theorem forallSmoothComparison.iff {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : GroupoidsOver S}
    (f : X ⟶ Y) :
    forallSmoothComparison P f ↔
      ∀ {U V : AlgebraicSpace S} (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
        (h : U ⟶ V),
        IsSmoothSpaceSquare f a b h → HasSmoothComparison f a b h → P h :=
  sorry

/-- The universal checking condition yields `forallSmoothComparison`. -/
theorem forallSmoothComparison.of {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)} {X Y : GroupoidsOver S}
    {f : X ⟶ Y}
    (hP : ∀ {U V : AlgebraicSpace S} (a : U.toGroupoids ⟶ X)
      (b : V.toGroupoids ⟶ Y) (h : U ⟶ V),
      IsSmoothSpaceSquare f a b h → HasSmoothComparison f a b h → P h) :
    forallSmoothComparison P f :=
  sorry

/-- Under `forallSmoothComparison`, the top arrow of a smooth algebraic-space
square with smooth comparison has `P`. -/
theorem forallSmoothComparison.spec {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)} {X Y : GroupoidsOver S}
    {f : X ⟶ Y} (hf : forallSmoothComparison P f) {U V : AlgebraicSpace S}
    (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y) (h : U ⟶ V)
    (hsq : IsSmoothSpaceSquare f a b h) (hφ : HasSmoothComparison f a b h) :
    P h :=
  sorry

/-- Some smooth algebraic-space square over `f` with surjective source atlas has
`P` on the top arrow. -/
def existsSurjectiveSmoothSquare {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : GroupoidsOver S}
    (f : X ⟶ Y) : Prop :=
  ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
    (h : U ⟶ V), IsSmoothSurjectivePresentation f a b h ∧ P h

/-- `existsSurjectiveSmoothSquare P f` is the existence of a smooth surjective
algebraic-space presentation whose top arrow has `P`. -/
theorem existsSurjectiveSmoothSquare.iff {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : GroupoidsOver S}
    (f : X ⟶ Y) :
    existsSurjectiveSmoothSquare P f ↔
      ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
        (h : U ⟶ V), IsSmoothSurjectivePresentation f a b h ∧ P h :=
  sorry

/-- A smooth surjective presentation whose top arrow has `P` witnesses
`existsSurjectiveSmoothSquare`. -/
theorem existsSurjectiveSmoothSquare.of {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)} {X Y : GroupoidsOver S}
    {f : X ⟶ Y} {U V : AlgebraicSpace S} (a : U.toGroupoids ⟶ X)
    (b : V.toGroupoids ⟶ Y) (h : U ⟶ V)
    (hpres : IsSmoothSurjectivePresentation f a b h) (hP : P h) :
    existsSurjectiveSmoothSquare P f :=
  sorry

/-- A witness of `existsSurjectiveSmoothSquare` supplies a smooth surjective
presentation whose top arrow has `P`. -/
theorem existsSurjectiveSmoothSquare.spec {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)} {X Y : GroupoidsOver S}
    {f : X ⟶ Y} (hf : existsSurjectiveSmoothSquare P f) :
    ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
      (h : U ⟶ V), IsSmoothSurjectivePresentation f a b h ∧ P h :=
  sorry

/-- For a property smooth local on source and target, a morphism of algebraic
stacks satisfies the property on every smooth square with smooth comparison if
and only if it does so on some smooth square with surjective source atlas. -/
theorem forallSmoothComparison_iff_existsSurjectiveSmoothSquare
    {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P] (f : X ⟶ Y) :
    forallSmoothComparison P f ↔ existsSurjectiveSmoothSquare P f :=
  sorry

/-- For a property smooth local on source and target, the universal smooth-square
condition on a morphism between algebraic spaces is equivalent to the property
of the evaluated algebraic-space morphism. -/
theorem forallSmoothComparison_iff_eval {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    {U V : AlgebraicSpace S} (f : U.toGroupoids ⟶ V.toGroupoids) :
    forallSmoothComparison P f ↔ P (AlgebraicSpace.toGroupoids.eval f) :=
  sorry

/-- For a property smooth local on source and target, stable under arbitrary
base change, and fppf local on the target, the universal smooth-square condition
on a morphism representable by algebraic spaces is equivalent to the property
tested on all scheme base changes. -/
theorem forallSmoothComparison_iff_has {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f) :
    forallSmoothComparison P f ↔ Groupoids.Hom.has P f :=
  sorry

/-- Transport of the universal smooth-square condition along equivalences with
algebraic spaces recovers the property of the induced algebraic-space morphism. -/
theorem forallSmoothComparison_iff_recover {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    {U V : AlgebraicSpace S} (eX : X ≌ U.toGroupoids)
    (eY : Y ≌ V.toGroupoids) (f : X ⟶ Y) :
    forallSmoothComparison P f ↔
      P (AlgebraicSpace.toGroupoids.recover eX eY f) :=
  sorry

/-- A morphism `f : X ⟶ Y` of algebraic stacks has a morphism property `P` of
algebraic spaces that is smooth local on the source-and-target when some smooth
algebraic-space presentation square with surjective source atlas has `P` on the
top arrow. -/
def hasSmoothLocalAtSourceAndTarget {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P] {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  existsSurjectiveSmoothSquare P f

/-- `hasSmoothLocalAtSourceAndTarget P f` is the existence of a smooth
surjective algebraic-space presentation whose top arrow has `P`. -/
theorem hasSmoothLocalAtSourceAndTarget_def {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P] {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    hasSmoothLocalAtSourceAndTarget P f ↔ existsSurjectiveSmoothSquare P f :=
  sorry

namespace hasSmoothLocalAtSourceAndTarget

/-- A smooth surjective algebraic-space presentation whose top arrow has `P`
witnesses `hasSmoothLocalAtSourceAndTarget P f`. -/
theorem of {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P] {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} {U V : AlgebraicSpace S}
    {a : U.toGroupoids ⟶ X} {b : V.toGroupoids ⟶ Y} {h : U ⟶ V}
    (hpres : IsSmoothSurjectivePresentation f a b h) (hP : P h) :
    hasSmoothLocalAtSourceAndTarget P f :=
  sorry

/-- A morphism satisfying `hasSmoothLocalAtSourceAndTarget P f` admits a smooth
surjective algebraic-space presentation whose top arrow has `P`. -/
theorem spec {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P] {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : hasSmoothLocalAtSourceAndTarget P f) :
    ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
      (h : U ⟶ V), IsSmoothSurjectivePresentation f a b h ∧ P h :=
  sorry

/-- An implication between morphism properties of algebraic spaces that are
smooth local on source and target induces the same implication between their
lifts to morphisms of algebraic stacks. -/
theorem of_le {S : Scheme.{u}} {P P' : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P'] (h : P ≤ P')
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    {f : X ⟶ Y} (hf : hasSmoothLocalAtSourceAndTarget P f) :
    hasSmoothLocalAtSourceAndTarget P' f :=
  sorry

end hasSmoothLocalAtSourceAndTarget

/-- A morphism of algebraic stacks has the smooth-local-on-source-and-target
lift of `P` if and only if every smooth algebraic-space presentation square
with smooth comparison has `P` on the top arrow. -/
theorem hasSmoothLocalAtSourceAndTarget_iff_forallSmoothComparison
    {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P] {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    hasSmoothLocalAtSourceAndTarget P f ↔ forallSmoothComparison P f :=
  sorry

/-- If `X` and `Y` are algebraic spaces, then `hasSmoothLocalAtSourceAndTarget P`
on the associated 1-morphism is equivalent to `P` on the evaluated morphism of
algebraic spaces. -/
theorem hasSmoothLocalAtSourceAndTarget_iff_eval {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P] {U V : AlgebraicSpace S}
    (f : U.toGroupoids ⟶ V.toGroupoids) :
    hasSmoothLocalAtSourceAndTarget P f ↔
      P (AlgebraicSpace.toGroupoids.eval f) :=
  sorry

/-- If `P` is also stable under base change and fppf local on the target, then
for a morphism representable by algebraic spaces the
smooth-local-on-source-and-target lift of `P` is equivalent to
`Groupoids.Hom.has P`. -/
theorem hasSmoothLocalAtSourceAndTarget_iff_has {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f) :
    hasSmoothLocalAtSourceAndTarget P f ↔ Groupoids.Hom.has P f :=
  sorry

/-- Transport of `hasSmoothLocalAtSourceAndTarget P` along presentations of
algebraic stacks by algebraic spaces recovers `P` on the induced morphism of
algebraic spaces. -/
theorem hasSmoothLocalAtSourceAndTarget_iff_recover {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    {U V : AlgebraicSpace S} (eX : X ≌ U.toGroupoids)
    (eY : Y ≌ V.toGroupoids) (f : X ⟶ Y) :
    hasSmoothLocalAtSourceAndTarget P f ↔
      P (AlgebraicSpace.toGroupoids.recover eX eY f) :=
  sorry

/-- A morphism of algebraic spaces that has `P` induces a 1-morphism of
algebraic stacks that has the smooth-local-on-source-and-target lift of `P`. -/
theorem hasSmoothLocalAtSourceAndTarget_map {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P] {U V : AlgebraicSpace S}
    {h : U ⟶ V} (hh : P h) :
    hasSmoothLocalAtSourceAndTarget P (AlgebraicSpace.toGroupoids.map h) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
