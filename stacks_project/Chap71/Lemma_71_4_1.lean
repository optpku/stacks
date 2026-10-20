/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fiber.LocallyNoetherian
public import stacks_project.Chap71.Lemma_71_4_1_Fiber

/-!
# Lemma 71.4.1

Local Noetherianity of a fibre of a morphism of algebraic spaces at a point of
the target is independent of the étale scheme chart, and equivalent to existence
of a field-valued representative whose fibre is locally Noetherian. A
monomorphic field-valued representative, when it exists, may be used as well.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.LocallyNoetherianFiber

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 71.4.1 (1): let `S` be a scheme, let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`, and let `y` be a point of `Points Y`. The following
are equivalent: there exist a scheme `V` over `S`, a point `v` of `V`, and an
étale morphism `a : ofOver V ⟶ Y` mapping `v` to `y` such that
`residueFiberOver f a v` is locally Noetherian; the same holds for every such
étale morphism; and there exists a field-valued point of `Y` representing `y`
such that `fieldFiber f p` is locally Noetherian. -/
@[stacks 0CUW]
#check (AlgebraicGeometry.AlgebraicSpace.locallyNoetherianFiber_tfae :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y),
    List.TFAE [existsEtale f y, forallEtale f y, existsField f y])

/- Lemma 71.4.1 (2): if in addition there is a monomorphism `p₀.hom` from the
spectrum of a field representing `y`, then the conditions of
`locallyNoetherianFiber_tfae` are also equivalent to `fieldFiber f p₀` being
locally Noetherian. -/
@[stacks 0CUW]
#check (AlgebraicGeometry.AlgebraicSpace.locallyNoetherianFiber_iff_of_mono :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y)
    (p₀ : FieldValuedPoint Y) [Mono p₀.hom] (hp₀ : Points.mk p₀ = y),
    IsLocallyNoetherian (fieldFiber f p₀) ↔ existsField f y)

end AlgebraicGeometry.AlgebraicSpace
