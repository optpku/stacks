module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.CartesianProperties
import StacksCheckRecall

open CategoryTheory Limits
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.10.3 (1): in a cartesian morphism of thickenings of algebraic spaces
whose two horizontal maps are locally of finite type, the closed map is locally
quasi-finite if and only if the ambient map is locally quasi-finite. -/
@[stacks 0BPJ] #check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.locallyQuasiFinite_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S}
    (g : T ⟶ U)
    [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType g.left]
    [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right),
    AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite g.left ↔
      AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite g.right)

/- Lemma 76.10.3 (2): in a cartesian morphism of thickenings of algebraic spaces
whose two horizontal maps are locally of finite type, the closed map is finite if
and only if the ambient map is finite. -/
@[stacks 0BPJ] #check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.isFinite_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S}
    (g : T ⟶ U)
    [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType g.left]
    [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right),
    AlgebraicGeometry.AlgebraicSpace.IsFinite g.left ↔
      AlgebraicGeometry.AlgebraicSpace.IsFinite g.right)

/- Lemma 76.10.3 (3): in a cartesian morphism of thickenings of algebraic spaces
whose two horizontal maps are locally of finite type, the closed map is a closed
immersion if and only if the ambient map is a closed immersion. -/
@[stacks 0BPJ] #check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.isClosedImmersion_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S}
    (g : T ⟶ U)
    [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType g.left]
    [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right),
    AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion g.left ↔
      AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion g.right)

/- Lemma 76.10.3 (4): in a cartesian morphism of thickenings of algebraic spaces
whose two horizontal maps are locally of finite type, the relative differentials
of the closed map vanish if and only if those of the ambient map vanish. -/
@[stacks 0BPJ] #check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.isZero_relativeDifferentials_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S}
    (g : T ⟶ U)
    [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType g.left]
    [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right),
    Limits.IsZero (Ω[g.left]) ↔ Limits.IsZero (Ω[g.right]))

/- Lemma 76.10.3 (5): in a cartesian morphism of thickenings of algebraic spaces
whose two horizontal maps are locally of finite type, the closed map is unramified
if and only if the ambient map is unramified. -/
@[stacks 0BPJ] #check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.unramified_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S}
    (g : T ⟶ U)
    [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType g.left]
    [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right),
    AlgebraicGeometry.AlgebraicSpace.Unramified g.left ↔
      AlgebraicGeometry.AlgebraicSpace.Unramified g.right)

/- Lemma 76.10.3 (6): in a cartesian morphism of thickenings of algebraic spaces
whose two horizontal maps are locally of finite type, the closed map is a
monomorphism if and only if the ambient map is a monomorphism. -/
@[stacks 0BPJ] #check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.mono_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S}
    (g : T ⟶ U)
    [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType g.left]
    [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right),
    Mono g.left ↔ Mono g.right)

/- Lemma 76.10.3 (7): in a cartesian morphism of thickenings of algebraic spaces
whose two horizontal maps are locally of finite type, the closed map is an
immersion if and only if the ambient map is an immersion. -/
@[stacks 0BPJ] #check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.isImmersion_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S}
    (g : T ⟶ U)
    [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType g.left]
    [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right),
    AlgebraicGeometry.AlgebraicSpace.IsImmersion g.left ↔
      AlgebraicGeometry.AlgebraicSpace.IsImmersion g.right)

/- Lemma 76.10.3 (8): in a cartesian morphism of thickenings of algebraic spaces
whose two horizontal maps are locally of finite type, the closed map is proper
if and only if the ambient map is proper. -/
@[stacks 0BPJ] #check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.proper_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S}
    (g : T ⟶ U)
    [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType g.left]
    [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right),
    AlgebraicGeometry.AlgebraicSpace.Proper g.left ↔
      AlgebraicGeometry.AlgebraicSpace.Proper g.right)
