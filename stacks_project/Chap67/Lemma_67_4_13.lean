/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Definition_67_4_2_Separation

/-!
# Representable morphisms of algebraic spaces and separation axioms

A representable morphism of algebraic spaces is locally separated. It is
separated (resp. quasi-separated) in the diagonal sense of Definition 67.4.2
if and only if it is separated (resp. quasi-separated) in the representable
sense of Section 67.3. On morphisms of schemes over `S` these two senses agree
with ordinary scheme-morphism (quasi-)separatedness.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.4.13 (1): let `S` be a scheme and let `f : X ⟶ Y` be a representable
morphism of algebraic spaces over `S`. Then `f` is locally separated. -/
@[stacks 03KY]
theorem locallySeparated_of_relativelyRepresentable
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) : LocallySeparated f :=
  sorry

/-- Lemma 67.4.13 (2): let `S` be a scheme and let `f : X ⟶ Y` be a representable
morphism of algebraic spaces over `S`. Then `f` is separated in the sense of
Definition 67.4.2 if and only if `f` is separated in the sense of Section 67.3. -/
@[stacks 03KY]
theorem separated_presheaf_iff_separated
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.IsSeparated : MorphismProperty Scheme.{u})).presheaf f ↔
      Separated f :=
  sorry

/-- A representable morphism that is separated in the sense of Section 67.3 is
separated as a morphism of algebraic spaces. -/
theorem separated_of_presheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    (h : (over (@AlgebraicGeometry.IsSeparated :
      MorphismProperty Scheme.{u})).presheaf f) :
    Separated f :=
  sorry

/-- A representable morphism that is separated as a morphism of algebraic spaces
is separated in the sense of Section 67.3. -/
theorem separated_presheaf_of_separated
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (h : Separated f) :
    (over (@AlgebraicGeometry.IsSeparated : MorphismProperty Scheme.{u})).presheaf f :=
  sorry

/-- Lemma 67.4.13 (3): let `S` be a scheme and let `f : X ⟶ Y` be a representable
morphism of algebraic spaces over `S`. Then `f` is quasi-separated in the sense of
Definition 67.4.2 if and only if `f` is quasi-separated in the sense of
Section 67.3. -/
@[stacks 03KY]
theorem quasiSeparated_presheaf_iff_quasiSeparated
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.QuasiSeparated : MorphismProperty Scheme.{u})).presheaf f ↔
      QuasiSeparated f :=
  sorry

/-- A representable morphism that is quasi-separated in the sense of Section 67.3
is quasi-separated as a morphism of algebraic spaces. -/
theorem quasiSeparated_of_presheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    (h : (over (@AlgebraicGeometry.QuasiSeparated :
      MorphismProperty Scheme.{u})).presheaf f) :
    QuasiSeparated f :=
  sorry

/-- A representable morphism that is quasi-separated as a morphism of algebraic
spaces is quasi-separated in the sense of Section 67.3. -/
theorem quasiSeparated_presheaf_of_quasiSeparated
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (h : QuasiSeparated f) :
    (over (@AlgebraicGeometry.QuasiSeparated : MorphismProperty Scheme.{u})).presheaf f :=
  sorry

/-- Lemma 67.4.13 (4): let `S` be a scheme and let `h : U ⟶ V` be a morphism of
schemes over `S`. Then the induced morphism of algebraic spaces is separated in
the sense of Definition 67.4.2 if and only if `h.left` is separated as a
morphism of schemes. -/
@[stacks 03KY]
theorem separated_ofOverMap_iff {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V) :
    Separated (ofOverMap h) ↔ AlgebraicGeometry.IsSeparated h.left :=
  sorry

/-- Lemma 67.4.13 (5): let `S` be a scheme and let `h : U ⟶ V` be a morphism of
schemes over `S`. Then the induced morphism of algebraic spaces is
quasi-separated in the sense of Definition 67.4.2 if and only if `h.left` is
quasi-separated as a morphism of schemes. -/
@[stacks 03KY]
theorem quasiSeparated_ofOverMap_iff {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) :
    QuasiSeparated (ofOverMap h) ↔ AlgebraicGeometry.QuasiSeparated h.left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
