/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia.Separation
import StacksCheckRecall

/-!
# Relative inertia versus the first diagonal

For a morphism of algebraic stacks, scheme-slice separation, quasi-separation,
and local separation of `I_{X/Y} ⟶ X` are equivalent to the same properties of
the first diagonal `Hom.diagonal f`, and to the identity section
`identitySection f : X ⟶ I_{X/Y}` being a closed immersion, quasi-compact, or
an immersion, respectively. Unramifiedness (resp. local quasi-finiteness) of
`I_{X/Y} ⟶ X` is equivalent to `f` being DM (resp. quasi-DM).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.RelativeInertia
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.RelativeInertia

/- Lemma 101.6.1 (1): the relative-inertia projection is separated iff the first
diagonal is separated iff the neutral section is a closed immersion. -/
@[stacks 0CL0] #check (AlgebraicGeometry.AlgebraicStack.RelativeInertia.forget_separated_tfae :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    List.TFAE
      [Groupoids.Hom.has (@AlgebraicSpace.Separated S)
          (forget.{u + 1, u, u, u + 1} f),
        Groupoids.Hom.has (@AlgebraicSpace.Separated S)
          (Hom.diagonal.{u + 1, u, u + 1} f),
        Groupoids.Hom.has (@AlgebraicSpace.IsClosedImmersion S)
          (identitySection.{u + 1, u, u, u + 1} f)])

/- Lemma 101.6.1 (2): the relative-inertia projection is quasi-separated iff the
first diagonal is quasi-separated iff the neutral section is quasi-compact. -/
@[stacks 0CL0] #check (AlgebraicGeometry.AlgebraicStack.RelativeInertia.forget_quasiSeparated_tfae :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    List.TFAE
      [Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
          (forget.{u + 1, u, u, u + 1} f),
        Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
          (Hom.diagonal.{u + 1, u, u + 1} f),
        Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S)
          (identitySection.{u + 1, u, u, u + 1} f)])

/- Lemma 101.6.1 (3): the relative-inertia projection is locally separated iff the
first diagonal is locally separated iff the neutral section is an immersion. -/
@[stacks 0CL0] #check (AlgebraicGeometry.AlgebraicStack.RelativeInertia.forget_locallySeparated_tfae :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    List.TFAE
      [Groupoids.Hom.has (@AlgebraicSpace.LocallySeparated S)
          (forget.{u + 1, u, u, u + 1} f),
        Groupoids.Hom.has (@AlgebraicSpace.LocallySeparated S)
          (Hom.diagonal.{u + 1, u, u + 1} f),
        Groupoids.Hom.has (@AlgebraicSpace.IsImmersion S)
          (identitySection.{u + 1, u, u, u + 1} f)])

/- Lemma 101.6.1 (4): the relative-inertia projection is unramified iff the
morphism of algebraic stacks is DM. -/
@[stacks 0CL0] #check (AlgebraicGeometry.AlgebraicStack.RelativeInertia.forget_unramified_iff_DM :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    Groupoids.Hom.has (@AlgebraicSpace.Unramified S)
        (forget.{u + 1, u, u, u + 1} f) ↔
      DM f)

/- Lemma 101.6.1 (5): the relative-inertia projection is locally quasi-finite iff
the morphism of algebraic stacks is quasi-DM. -/
@[stacks 0CL0] #check (AlgebraicGeometry.AlgebraicStack.RelativeInertia.forget_locallyQuasiFinite_iff_quasiDM :
    ∀ {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y),
    Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S)
        (forget.{u + 1, u, u, u + 1} f) ↔
      QuasiDM f)

end AlgebraicGeometry.AlgebraicStack.RelativeInertia
