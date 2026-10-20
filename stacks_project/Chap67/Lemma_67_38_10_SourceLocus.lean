/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_13_1_SchematicLocus
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap67.Lemma_67_23_3_Pullback
public import stacks_project.Chap67.Lemma_67_23_6_Cancellation
public import stacks_project.Chap67.Lemma_67_38_5_Unramified

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.SourceLocus

/-!
# Unramified source locus of a morphism of algebraic spaces

Typed checks of the canonical source locus and its base-change laws.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Unramified

#check (AlgebraicGeometry.AlgebraicSpace.Unramified.isOpen_unramifiedAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y), IsOpen (setOf (UnramifiedAt f)))

#check (AlgebraicGeometry.AlgebraicSpace.Unramified.sourceLocus :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    OpenSubspace X)

#check (AlgebraicGeometry.AlgebraicSpace.Unramified.sourceLocus_unramified :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y), Unramified ((sourceLocus f).ι ≫ f))

#check (AlgebraicGeometry.AlgebraicSpace.Unramified.sourceLocus_pointsSet_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y),
    (sourceLocus f).pointsSet = {x | UnramifiedAt f x})

#check (AlgebraicGeometry.AlgebraicSpace.Unramified.mem_sourceLocus :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X),
    x ∈ (sourceLocus f).pointsSet ↔ UnramifiedAt f x)

#check (AlgebraicGeometry.AlgebraicSpace.Unramified.sourceLocus_maximal :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {U : AlgebraicSpace S} (i : U ⟶ X) [IsOpenImmersion i]
    (hf : Unramified (i ≫ f)),
    Set.range (Points.map i) ⊆ (sourceLocus f).pointsSet)

#check (AlgebraicGeometry.AlgebraicSpace.Unramified.overBaseChange :
  ∀ {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z),
    pullback (f ≫ q) g ⟶ pullback q g)

#check (AlgebraicGeometry.AlgebraicSpace.Unramified.overBaseChange_fst :
  ∀ {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z),
    overBaseChange f q g ≫ pullback.fst q g =
      pullback.fst (f ≫ q) g ≫ f)

#check (AlgebraicGeometry.AlgebraicSpace.Unramified.overBaseChange_snd :
  ∀ {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z),
    overBaseChange f q g ≫ pullback.snd q g =
      pullback.snd (f ≫ q) g)

#check (AlgebraicGeometry.AlgebraicSpace.Unramified.unramifiedAt_iff_of_isPullback :
  ∀ {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hpb : IsPullback g' f' f g) [LocallyOfFiniteType f]
    (x' : Points X'),
    UnramifiedAt f' x' ↔ UnramifiedAt f (Points.map g' x'))

#check (AlgebraicGeometry.AlgebraicSpace.Unramified.sourceLocus_eq_preimage_of_isPullback :
  ∀ {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hpb : IsPullback g' f' f g) [LocallyOfFiniteType f],
    (sourceLocus f').pointsSet = Points.map g' ⁻¹' (sourceLocus f).pointsSet)

#check (AlgebraicGeometry.AlgebraicSpace.Unramified.sourceLocus_pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y' ⟶ Y),
    (sourceLocus (pullback.snd f g)).pointsSet =
      Points.map (pullback.fst f g) ⁻¹' (sourceLocus f).pointsSet)

end Unramified

end AlgebraicGeometry.AlgebraicSpace
