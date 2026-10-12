/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.Fiber.Basic
public import ReasLib.RingTheory.RingHom.Local.Properties
import StacksCheckRecall

/-
Lemma 29.14.7 (1): isomorphism on the local rings at every prime of the target
is a local property of a commutative ring map.
-/
@[stacks 01SX] #check
  (RingHom.IsIsoOnLocalRings.propertyIsLocal :
    RingHom.PropertyIsLocal RingHom.IsIsoOnLocalRings)

/-
Lemma 29.14.7 (2): the affine open-immersion condition expressed by bijectivity
on suitable source principal localizations is a local property of a
commutative ring map.
-/
@[stacks 01SX] #check
  (RingHom.IsOpenImmersion.propertyIsLocal :
    RingHom.PropertyIsLocal RingHom.IsOpenImmersion)

/-
Lemma 29.14.7 (3): having reduced residue-field fibers is a local property of a
commutative ring map.
-/
@[stacks 01SX] #check
  (RingHom.HasReducedFibers.propertyIsLocal :
    RingHom.PropertyIsLocal RingHom.HasReducedFibers)

/-
Lemma 29.14.7 (4): having residue-field fibers of Krull dimension at most a
fixed `n : Nat` is a local property of a commutative ring map.
-/
@[stacks 01SX] #check
  (RingHom.FibersKrullDimLE.propertyIsLocal :
    ∀ n : Nat, RingHom.PropertyIsLocal (RingHom.FibersKrullDimLE n))

/-
Lemma 29.14.7 (5): having Noetherian target is a local property of a
commutative ring map.
-/
@[stacks 01SX] #check
  (RingHom.TargetIsNoetherian.propertyIsLocal :
    RingHom.PropertyIsLocal RingHom.TargetIsNoetherian)
