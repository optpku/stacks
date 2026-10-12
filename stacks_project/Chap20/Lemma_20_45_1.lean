/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Gluing.TwoOpen

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived.Gluing

/-
Lemma 20.45.1: derived modules on two opens `U` and `V` covering a ringed space glue when their
restrictions to `U ⊓ V` are isomorphic.  Moreover, compatible local morphisms from a fixed gluing
to an ambient target extend to a global morphism.

The reusable owner keeps the direct-versus-iterated restriction transport explicit as
`TwoOpen.overlapIso`; its predicates infer the opens and ambient objects from the local object and
morphism types.
-/

@[stacks 08DG "Lemma 20.45.1 (1): existence of a two-open derived gluing"]
#check @TwoOpen.existsObj

@[stacks 08DG "Lemma 20.45.1 (2): extension of compatible local morphisms"]
#check @TwoOpen.existsHom

@[stacks 08DG "two-open overlap restriction isomorphism"]
#check @TwoOpen.overlapIso
@[stacks 08DG "two-open derived gluing datum"]
#check @TwoOpen.IsGluing
@[stacks 08DG "two-open gluing commutative square"]
#check @TwoOpen.IsGluing.commSq
@[stacks 08DG "two-open gluing object"]
#check @TwoOpen.IsGluing.w
@[stacks 08DG "two-open morphism compatibility"]
#check @TwoOpen.Compatible
@[stacks 08DG "two-open compatible morphism square"]
#check @TwoOpen.Compatible.commSq
@[stacks 08DG "two-open compatible morphism"]
#check @TwoOpen.Compatible.w

end
