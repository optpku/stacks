/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Separated
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap67.Lemma_67_28_5
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap79.Proposition_79_12_11

/-!
# The finite part of a separated flat locally finite-presentation morphism

If `f : X ⟶ Y` is separated, flat, and locally of finite presentation, then
the structure morphism `(X/Y)_fin ⟶ Y` is separated, representable, and
étale, and if `Y` is a scheme then `(X/Y)_fin` is a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

/- Lemma 79.12.14 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is separated, flat, and locally of finite
presentation. Then the structure morphism `spaceHom f : space f ⟶ Y`, i.e.
`(X/Y)_fin ⟶ Y`, is separated, representable, and étale. The étale clause is
`instEtale_spaceHom`. -/
@[stacks 04RI] #check (AlgebraicGeometry.AlgebraicSpace.FinitePart.instSeparated_spaceHom :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] [Flat f] [LocallyOfFinitePresentation f], Separated (spaceHom f))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.relativelyRepresentable_spaceHom :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] [Flat f] [LocallyOfFinitePresentation f],
    yoneda.relativelyRepresentable (spaceHom f))

section

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
  [Separated f] [Flat f] [LocallyOfFinitePresentation f]

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.instEtale_spaceHom f :
  Etale (spaceHom f))

end

/- Lemma 79.12.14 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is separated, flat, and locally of finite
presentation. If `Y` is a scheme, then `(X/Y)_fin` is a scheme. -/
@[stacks 04RI] #check (AlgebraicGeometry.AlgebraicSpace.FinitePart.instIsScheme_space :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] [Flat f] [LocallyOfFinitePresentation f] [IsScheme Y], IsScheme (space f))

end AlgebraicGeometry.AlgebraicSpace.FinitePart
