/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic
public import stacks_project.Chap67.Definition_67_46_2_FiniteLocallyFree

/-!
# Representable finite locally free morphisms of algebraic spaces

A representable morphism of algebraic spaces is finite locally free in the
sense of Section 67.3 if and only if it is affine and the direct image of its
structure sheaf is a finite locally free module on the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.46.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a representable
morphism of algebraic spaces over `S`. Then `f` is finite locally free in the
sense of Section 67.3 if and only if `f` is affine and the sheaf `f_* 𝒪_X` is a
finite locally free `𝒪_Y`-module. -/
@[stacks 03ZU]
theorem finiteLocallyFree_presheaf_iff
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.IsFiniteLocallyFree :
      MorphismProperty Scheme.{u})).presheaf f ↔
      Affine f ∧ SheafOfModules.IsFiniteLocallyFree f.pushforwardStructureModule :=
  sorry

/-- For a representable morphism, Section 67.3 finite local freeness is equivalent
to the algebraic-space finite locally free class. -/
theorem finiteLocallyFree_presheaf_iff_finiteLocallyFree
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.IsFiniteLocallyFree :
      MorphismProperty Scheme.{u})).presheaf f ↔
      FiniteLocallyFree f :=
  sorry

/-- A representable morphism that is finite locally free in the sense of
Section 67.3 is affine and has finite locally free pushforward structure sheaf. -/
theorem affine_and_pushforwardStructureModule_of_presheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    (h : (over (@AlgebraicGeometry.IsFiniteLocallyFree :
      MorphismProperty Scheme.{u})).presheaf f) :
    Affine f ∧ SheafOfModules.IsFiniteLocallyFree f.pushforwardStructureModule :=
  sorry

/-- A representable morphism that is affine with finite locally free pushforward
structure sheaf is finite locally free in the sense of Section 67.3. -/
theorem finiteLocallyFree_presheaf_of_affine_and_pushforward
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (hAffine : Affine f)
    (hMod : SheafOfModules.IsFiniteLocallyFree f.pushforwardStructureModule) :
    (over (@AlgebraicGeometry.IsFiniteLocallyFree :
      MorphismProperty Scheme.{u})).presheaf f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
