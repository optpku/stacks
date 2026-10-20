/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Henselian
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.EtaleFreeOpen
public import ReasLib.LinearAlgebra.UniversallyInjective.Quotient
public import ReasLib.RingTheory.Flatness.MittagLeffler.Colimit
public import ReasLib.RingTheory.Flatness.MittagLeffler.Equiv
public import ReasLib.RingTheory.Flatness.MittagLeffler.Projective

/-!
# Mittag-Leffler modules over henselian local rings

Finite flat modules over essentially finite-type local algebras over a henselian local ring
have free directed presentations with closed-fiber-injective transition maps and are
Mittag-Leffler over the base.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace Module.Flat

/-- A finite module over an essentially finite-type local algebra, flat over a henselian local
base, has a directed colimit presentation by free modules whose transition maps remain injective
after reduction modulo the maximal ideal of the base. -/
@[stacks 05U7]
theorem exists_freePresentation_of_henselian
    {A B N : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [HenselianLocalRing A]
    [IsLocalRing B]
    [IsLocalHom (algebraMap A B)]
    [Algebra.EssFiniteType A B]
    [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N] [Module.Finite B N] [Module.Flat A N] :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirectedOrder I)
      (P : ColimitPresentation I (ModuleCat.of A N)),
      (∀ i, Module.Free A (P.diag.obj i)) ∧
        ∀ ⦃i j : I⦄ (hij : i ≤ j),
          Function.Injective
            ((P.diag.map (homOfLE hij)).hom.quotientMapByIdeal (maximalIdeal A)) := sorry

end Module.Flat

namespace Module.MittagLeffler

/-- A finite module over an essentially finite-type local algebra, flat over a henselian local
base, is Mittag-Leffler over the base. -/
@[stacks 05U7]
theorem of_henselian_base
    {A B N : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [HenselianLocalRing A]
    [IsLocalRing B]
    [IsLocalHom (algebraMap A B)]
    [Algebra.EssFiniteType A B]
    [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N] [Module.Finite B N] [Module.Flat A N] :
    Module.MittagLeffler A N := sorry

end Module.MittagLeffler
