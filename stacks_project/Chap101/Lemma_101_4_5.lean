/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Covering
import StacksCheckRecall

/-!
# Descent of separation axioms along fppf algebraic-space coverings
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.DM

/- Lemma 101.4.5 (1): DM descends along a surjective, flat,
locally of finite presentation morphism from an algebraic space. -/
@[stacks 06TZ]
#check (AlgebraicGeometry.AlgebraicStack.DM.of_covering :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    [DM (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)],
    DM f)

#check (AlgebraicGeometry.AlgebraicStack.DM.of_isBilimit_covering :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    {W : AlgebraicSpace S} {g : W.toGroupoids ⟶ Y}
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt],
    c.IsBilimit → ∀ [DM c.snd], DM f)

end AlgebraicGeometry.AlgebraicStack.DM

namespace AlgebraicGeometry.AlgebraicStack.QuasiDM

/- Lemma 101.4.5 (2): quasi-DM descends along a surjective, flat,
locally of finite presentation morphism from an algebraic space. -/
@[stacks 06TZ]
#check (AlgebraicGeometry.AlgebraicStack.QuasiDM.of_covering :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    [QuasiDM (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)],
    QuasiDM f)

#check (AlgebraicGeometry.AlgebraicStack.QuasiDM.of_isBilimit_covering :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    {W : AlgebraicSpace S} {g : W.toGroupoids ⟶ Y}
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt],
    c.IsBilimit → ∀ [QuasiDM c.snd], QuasiDM f)

end AlgebraicGeometry.AlgebraicStack.QuasiDM

namespace AlgebraicGeometry.AlgebraicStack.Separated

/- Lemma 101.4.5 (3): separated descends along a surjective, flat,
locally of finite presentation morphism from an algebraic space. -/
@[stacks 06TZ]
#check (AlgebraicGeometry.AlgebraicStack.Separated.of_covering :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    [Separated (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)],
    Separated f)

#check (AlgebraicGeometry.AlgebraicStack.Separated.of_isBilimit_covering :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    {W : AlgebraicSpace S} {g : W.toGroupoids ⟶ Y}
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt],
    c.IsBilimit → ∀ [Separated c.snd], Separated f)

end AlgebraicGeometry.AlgebraicStack.Separated

namespace AlgebraicGeometry.AlgebraicStack.QuasiSeparated

/- Lemma 101.4.5 (4): quasi-separated descends along a surjective, flat,
locally of finite presentation morphism from an algebraic space. -/
@[stacks 06TZ]
#check (AlgebraicGeometry.AlgebraicStack.QuasiSeparated.of_covering :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    [QuasiSeparated (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)],
    QuasiSeparated f)

#check (AlgebraicGeometry.AlgebraicStack.QuasiSeparated.of_isBilimit_covering :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    {W : AlgebraicSpace S} {g : W.toGroupoids ⟶ Y}
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt],
    c.IsBilimit → ∀ [QuasiSeparated c.snd], QuasiSeparated f)

end AlgebraicGeometry.AlgebraicStack.QuasiSeparated
