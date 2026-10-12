/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact

/-!
# Quasi-compact morphisms of algebraic spaces

The canonical owner supplies the original quasi-compactness predicate, its
universal-base-change description, and the identity, isomorphism and pullback APIs.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits MorphismProperty

universe u

#check (@quasiCompactSource : {S : Scheme.{u}} → MorphismProperty (AlgebraicSpace S))
#check (quasiCompactSource_iff : {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (f : X ⟶ Y) →
  quasiCompactSource f ↔ (IsQuasiCompact Y → IsQuasiCompact X))
#check (QuasiCompact : {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (X ⟶ Y) → Prop)
#check (QuasiCompact.id : {S : Scheme.{u}} → {X : AlgebraicSpace S} → QuasiCompact (𝟙 X))
#check (QuasiCompact.of_isIso : {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (f : X ⟶ Y) →
  [IsIso f] → QuasiCompact f)
#check (QuasiCompact.spec : {S : Scheme.{u}} → {X Y Z P : AlgebraicSpace S} →
  {f : X ⟶ Y} → {g : Z ⟶ Y} → {pZ : P ⟶ Z} → {pX : P ⟶ X} →
  [QuasiCompact f] → [IsQuasiCompact Z] → IsPullback pZ pX g f → IsQuasiCompact P)
#check (QuasiCompact.isQuasiCompact : {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (f : X ⟶ Y) →
  [QuasiCompact f] → [IsQuasiCompact Y] → IsQuasiCompact X)
#check (quasiCompact_iff_universally : {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (f : X ⟶ Y) →
  QuasiCompact f ↔ universally quasiCompactSource f)
#check (instIsQuasiCompact_pullback : {S : Scheme.{u}} → {X Y Z : AlgebraicSpace S} →
  (f : X ⟶ Y) → (g : Z ⟶ Y) → [QuasiCompact f] → [IsQuasiCompact Z] → [HasPullback f g] →
  IsQuasiCompact (pullback f g))
