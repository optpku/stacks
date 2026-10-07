module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap100.Lemma_100_11_1_Flat
public import stacks_project.Chap101.Definition_101_4_1_Separation

/-!
# Descent of separation axioms along fppf algebraic-space coverings

Each of the separation axioms of Definition 101.4.1 for a morphism of
algebraic stacks follows from the corresponding property of its base change
along a surjective, flat, locally of finite presentation morphism from an
algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.DM

/-- Lemma 101.4.5 (1): Let `f : X ⟶ Y` be a morphism of algebraic stacks, and
let `g : W.toGroupoids ⟶ Y` be a `Groupoids.Hom.Surjective`,
`Groupoids.Hom.Flat`, and `Groupoids.Hom.LocallyOfFinitePresentation`
morphism from an algebraic space `W`. If the base change
`TwoFibreProduct.snd f g` is DM, then `f` is DM.

Stacks writes the base change as `W ×_Y X ⟶ W`; the Lean projection is
`TwoFibreProduct.snd f g`. -/
@[stacks 06TZ]
theorem of_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)]
    [DM (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)] :
    DM f :=
  sorry

/-- DM of a morphism of algebraic stacks follows from DM of the second
projection of a bilimit `PseudoPullbackCone` against a surjective, flat,
locally of finite presentation morphism from an algebraic space. -/
theorem of_isBilimit_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    {W : AlgebraicSpace S} {g : W.toGroupoids ⟶ Y}
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    [DM c.snd] :
    DM f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.DM

namespace AlgebraicGeometry.AlgebraicStack.QuasiDM

/-- Lemma 101.4.5 (2): Let `f : X ⟶ Y` be a morphism of algebraic stacks, and
let `g : W.toGroupoids ⟶ Y` be a `Groupoids.Hom.Surjective`,
`Groupoids.Hom.Flat`, and `Groupoids.Hom.LocallyOfFinitePresentation`
morphism from an algebraic space `W`. If the base change
`TwoFibreProduct.snd f g` is quasi-DM, then `f` is quasi-DM.

Stacks writes the base change as `W ×_Y X ⟶ W`; the Lean projection is
`TwoFibreProduct.snd f g`. -/
@[stacks 06TZ]
theorem of_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)]
    [QuasiDM (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)] :
    QuasiDM f :=
  sorry

/-- Quasi-DM of a morphism of algebraic stacks follows from quasi-DM of the
second projection of a bilimit `PseudoPullbackCone` against a surjective,
flat, locally of finite presentation morphism from an algebraic space. -/
theorem of_isBilimit_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    {W : AlgebraicSpace S} {g : W.toGroupoids ⟶ Y}
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    [QuasiDM c.snd] :
    QuasiDM f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.QuasiDM

namespace AlgebraicGeometry.AlgebraicStack.Separated

/-- Lemma 101.4.5 (3): Let `f : X ⟶ Y` be a morphism of algebraic stacks, and
let `g : W.toGroupoids ⟶ Y` be a `Groupoids.Hom.Surjective`,
`Groupoids.Hom.Flat`, and `Groupoids.Hom.LocallyOfFinitePresentation`
morphism from an algebraic space `W`. If the base change
`TwoFibreProduct.snd f g` is separated, then `f` is separated.

Stacks writes the base change as `W ×_Y X ⟶ W`; the Lean projection is
`TwoFibreProduct.snd f g`. -/
@[stacks 06TZ]
theorem of_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)]
    [Separated (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)] :
    Separated f :=
  sorry

/-- Separatedness of a morphism of algebraic stacks follows from separatedness
of the second projection of a bilimit `PseudoPullbackCone` against a
surjective, flat, locally of finite presentation morphism from an algebraic
space. -/
theorem of_isBilimit_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    {W : AlgebraicSpace S} {g : W.toGroupoids ⟶ Y}
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    [Separated c.snd] :
    Separated f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Separated

namespace AlgebraicGeometry.AlgebraicStack.QuasiSeparated

/-- Lemma 101.4.5 (4): Let `f : X ⟶ Y` be a morphism of algebraic stacks, and
let `g : W.toGroupoids ⟶ Y` be a `Groupoids.Hom.Surjective`,
`Groupoids.Hom.Flat`, and `Groupoids.Hom.LocallyOfFinitePresentation`
morphism from an algebraic space `W`. If the base change
`TwoFibreProduct.snd f g` is quasi-separated, then `f` is quasi-separated.

Stacks writes the base change as `W ×_Y X ⟶ W`; the Lean projection is
`TwoFibreProduct.snd f g`. -/
@[stacks 06TZ]
theorem of_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)]
    [QuasiSeparated (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)] :
    QuasiSeparated f :=
  sorry

/-- Quasi-separatedness of a morphism of algebraic stacks follows from
quasi-separatedness of the second projection of a bilimit
`PseudoPullbackCone` against a surjective, flat, locally of finite
presentation morphism from an algebraic space. -/
theorem of_isBilimit_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    {W : AlgebraicSpace S} {g : W.toGroupoids ⟶ Y}
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    [QuasiSeparated c.snd] :
    QuasiSeparated f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.QuasiSeparated
