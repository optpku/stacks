/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Birational.Integral
import StacksCheckRecall

/-!
# Integral birational morphisms of decent algebraic spaces with normal target

An integral birational morphism of decent algebraic spaces with finitely many
irreducible components is an isomorphism when the target is normal and the
source is reduced.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsBirational

/- Lemma 68.22.8: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `X` and `Y` are decent and have finitely many
irreducible components, `f` is integral and birational, `Y` is normal, and `X`
is reduced. Then `f` is an isomorphism. -/
@[stacks 0B4E] #check
  (AlgebraicGeometry.AlgebraicSpace.IsBirational.isIso_of_isIntegralHom_of_isNormal :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    [IsReduced X] [IsNormal Y] (f : X ⟶ Y) [IsBirational f] [IsIntegralHom f],
    IsIso f)

end AlgebraicGeometry.AlgebraicSpace.IsBirational
