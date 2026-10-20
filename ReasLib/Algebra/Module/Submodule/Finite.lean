module

public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite Submodules

Mathlib already identifies finite modules with finitely generated top submodules and supplies the
specialization from a finite submodule to `Submodule.FG`.  This leaf is a stable import surface for
those canonical owners (`Module.Finite.fg_top`, `Module.Finite.iff_fg`, `Submodule.FG.of_finite`);
it deliberately introduces no parallel wrapper theorem.
-/

@[expose] public section
