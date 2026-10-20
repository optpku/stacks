module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.LinearSystem.VanishingLocus.ClosedPoints

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.LinearSystem
open scoped AlgebraicGeometry

universe u

/- Exercise 111.46.1: the tautological incidence subscheme of a projective linear system
contains a closed point exactly when the corresponding linear combination vanishes. -/
@[stacks 0EG9] #check (AlgebraicGeometry.LinearSystem.closedPoint_mem_vanishingIdeal_iff :
  ∀
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Curve X] [Projective X.hom]
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (n : ℕ) (s : Fin (n + 1) → SchemeOverField.globalSectionsMod X L)
    {v : Fin (n + 1) → k} (hv : v ≠ 0)
    {x : X.left} (hx : x ∈ closedPoints X.left)
    {z : product X n} (hz : z ∈ closedPoints (product X n))
    (hfst : fst X n z =
      ProjectiveSpace.homOf (RingHom.id k) hv (IsLocalRing.closedPoint k))
    (hsnd : snd X n z = x),
    z ∈ (vanishingIdeal X L n s).support ↔
      x ∉ RingedSpace.sectionNonvanishingLocus X.left.toRingedSpace L
        (linearCombination X L n s v))
