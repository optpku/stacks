/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Morphisms.Thickening.Cartesian
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.3.4 (1): in a cartesian morphism of thickenings whose two horizontal maps
are locally of finite type, the closed map is locally quasi-finite if and only if the ambient
map is locally quasi-finite. -/
@[stacks 0BPG] #check (AlgebraicGeometry.Thickening.Hom.locallyQuasiFinite_iff :
  ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U)
    [AlgebraicGeometry.LocallyOfFiniteType g.left]
    [AlgebraicGeometry.LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right),
    AlgebraicGeometry.LocallyQuasiFinite g.left ↔
      AlgebraicGeometry.LocallyQuasiFinite g.right)

/- Lemma 37.3.4 (2): in a cartesian morphism of thickenings whose two horizontal maps
are locally of finite type, the closed map is finite if and only if the ambient map is finite. -/
@[stacks 0BPG] #check (AlgebraicGeometry.Thickening.Hom.isFinite_iff :
  ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U)
    [AlgebraicGeometry.LocallyOfFiniteType g.left]
    [AlgebraicGeometry.LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right),
    AlgebraicGeometry.IsFinite g.left ↔ AlgebraicGeometry.IsFinite g.right)

/- Lemma 37.3.4 (3): in a cartesian morphism of thickenings whose two horizontal maps
are locally of finite type, the closed map is a closed immersion if and only if the ambient map
is a closed immersion. -/
@[stacks 0BPG] #check (AlgebraicGeometry.Thickening.Hom.isClosedImmersion_iff :
  ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U)
    [AlgebraicGeometry.LocallyOfFiniteType g.left]
    [AlgebraicGeometry.LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right),
    AlgebraicGeometry.IsClosedImmersion g.left ↔
      AlgebraicGeometry.IsClosedImmersion g.right)

/- Lemma 37.3.4 (4): in a cartesian morphism of thickenings whose two horizontal maps
are locally of finite type, the relative differentials of the closed map vanish if and only if
those of the ambient map vanish. -/
@[stacks 0BPG] #check (AlgebraicGeometry.Thickening.Hom.isZero_relativeDifferentials_iff :
  ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U)
    [AlgebraicGeometry.LocallyOfFiniteType g.left]
    [AlgebraicGeometry.LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right),
    Limits.IsZero (Ω[g.left.toShHom]) ↔ Limits.IsZero (Ω[g.right.toShHom]))

/- Lemma 37.3.4 (5): in a cartesian morphism of thickenings whose two horizontal maps
are locally of finite type, the closed map is unramified if and only if the ambient map is
unramified. -/
@[stacks 0BPG] #check (AlgebraicGeometry.Thickening.Hom.unramified_iff :
  ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U)
    [AlgebraicGeometry.LocallyOfFiniteType g.left]
    [AlgebraicGeometry.LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right),
    AlgebraicGeometry.Unramified g.left ↔ AlgebraicGeometry.Unramified g.right)

/- Lemma 37.3.4 (6): in a cartesian morphism of thickenings whose two horizontal maps
are locally of finite type, the closed map is a monomorphism if and only if the ambient map is a
monomorphism. -/
@[stacks 0BPG] #check (AlgebraicGeometry.Thickening.Hom.mono_iff :
  ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U)
    [AlgebraicGeometry.LocallyOfFiniteType g.left]
    [AlgebraicGeometry.LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right), Mono g.left ↔ Mono g.right)

/- Lemma 37.3.4 (7): in a cartesian morphism of thickenings whose two horizontal maps
are locally of finite type, the closed map is an immersion if and only if the ambient map is an
immersion. -/
@[stacks 0BPG] #check (AlgebraicGeometry.Thickening.Hom.isImmersion_iff :
  ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U)
    [AlgebraicGeometry.LocallyOfFiniteType g.left]
    [AlgebraicGeometry.LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right),
    AlgebraicGeometry.IsImmersion g.left ↔ AlgebraicGeometry.IsImmersion g.right)

/- Lemma 37.3.4 (8): in a cartesian morphism of thickenings whose two horizontal maps
are locally of finite type, the closed map is proper if and only if the ambient map is proper. -/
@[stacks 0BPG] #check (AlgebraicGeometry.Thickening.Hom.isProper_iff :
  ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U)
    [AlgebraicGeometry.LocallyOfFiniteType g.left]
    [AlgebraicGeometry.LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right),
    AlgebraicGeometry.IsProper g.left ↔ AlgebraicGeometry.IsProper g.right)
