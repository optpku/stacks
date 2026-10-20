/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap66.Definition_66_4_1_Points
import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeObjectProperty

/-!
# Fibres of relative conditions

A morphism of algebraic spaces has a relative object-level condition such as (β),
decent, reasonable, or very reasonable when, loosely speaking, its fibres have that
property. The precise test is scheme-base-change of the source; field-valued fibres
are the informal special case.
-/

/- Field-valued fibres arise by specializing the scheme test object to
`Over.mk y.structureHom` and the map to `y.hom`. The informal description is not a
converse criterion based only on field-valued fibres. Decency is useful for
specializations of points on `|X|`; reasonableness is stronger and technically easy
to work with. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Remark 68.17.10 -/
@[stacks 03L4] #check (AlgebraicGeometry.AlgebraicSpace.IsRelatively.spec :
    {S : Scheme.{u}} → {P : ObjectProperty (AlgebraicSpace S)} →
    {X Y W : AlgebraicSpace S} → {f : X ⟶ Y} → {T : Over S} →
    {g : ofOver T ⟶ Y} → {pT : W ⟶ ofOver T} → {pX : W ⟶ X} →
    [IsRelatively P f] → IsPullback pT pX g f → P W)

#check (AlgebraicGeometry.AlgebraicSpace.PropertyBeta.spec :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → {f : X ⟶ Y} →
    [PropertyBeta f] → {T : Over S} → {P : AlgebraicSpace S} →
    {g : ofOver T ⟶ Y} → {pT : P ⟶ ofOver T} → {pX : P ⟶ X} →
    IsPullback pT pX g f → HasPropertyBeta P)

#check (AlgebraicGeometry.AlgebraicSpace.Decent.spec :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → {f : X ⟶ Y} →
    [Decent f] → {T : Over S} → {P : AlgebraicSpace S} →
    {g : ofOver T ⟶ Y} → {pT : P ⟶ ofOver T} → {pX : P ⟶ X} →
    IsPullback pT pX g f → IsDecent P)

#check (AlgebraicGeometry.AlgebraicSpace.Reasonable.spec :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → {f : X ⟶ Y} →
    [Reasonable f] → {T : Over S} → {P : AlgebraicSpace S} →
    {g : ofOver T ⟶ Y} → {pT : P ⟶ ofOver T} → {pX : P ⟶ X} →
    IsPullback pT pX g f → IsReasonable P)

#check (AlgebraicGeometry.AlgebraicSpace.VeryReasonable.spec :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → {f : X ⟶ Y} →
    [VeryReasonable f] → {T : Over S} → {W : AlgebraicSpace S} →
    {g : ofOver T ⟶ Y} → {pT : W ⟶ ofOver T} → {pX : W ⟶ X} →
    IsPullback pT pX g f → IsVeryReasonable W)

end AlgebraicGeometry.AlgebraicSpace
