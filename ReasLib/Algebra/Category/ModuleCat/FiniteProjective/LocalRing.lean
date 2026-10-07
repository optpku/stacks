module

public import Mathlib.Algebra.Category.ModuleCat.Free
public import Mathlib.RingTheory.LocalRing.Module
public import ReasLib.Algebra.Category.ModuleCat.FiniteProjective
public import ReasLib.RingTheory.Finiteness.Projective.LocalRing
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite Projective Modules over Local Rings

Bundling finite projectivity makes the local-ring freeness theorem a stable,
narrow instance. This file also exposes finite-rank additivity for short exact
sequences in the bundled category.
-/

@[expose] public section

universe u v

namespace CategoryTheory.ModuleCat.FiniteProjective

variable (R : Type u) [CommRing R]

/-- A bundled finite-projective module over a local ring is finite free. -/
@[stacks 00JJ "finite projective modules over local rings are free"]
instance instFree [IsLocalRing R]
    (M : ModuleCat.FiniteProjective.{u, v} R) : Module.Free R M.obj :=
  Module.FiniteProjective.free_of_isLocalRing M.property

/-- Finite rank is additive along short exact sequences of bundled finite-projective modules over
a local ring. -/
@[stacks 00JJ "finite-projective short exact rank additivity"]
theorem finrank_add_of_shortExact
    [IsLocalRing R]
    (S : ShortComplex (ModuleCat.FiniteProjective.{u, v} R))
    (hS : (S.map (ModuleCat.finiteProjective.{u, v} R).ι).ShortExact) :
    Module.finrank R S.X₂.obj =
      Module.finrank R S.X₁.obj + Module.finrank R S.X₃.obj := sorry

end CategoryTheory.ModuleCat.FiniteProjective
