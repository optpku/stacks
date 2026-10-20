module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.Algebra.Category.ModuleCat.CharacterModule.Functor.MonoEpi
public import ReasLib.Algebra.Module.CharacterModule.Exact
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Exactness of the character-module functor
-/

open CategoryTheory

universe u v

namespace CharacterModule

/-- Character duality is an exact contravariant functor on modules over a
commutative ring. -/
@[stacks 01DA "exactness of the character-module functor"]
theorem exact (R : Type u) [CommRing R] :
    exactFunctor (ModuleCat.{v} R)ᵒᵖ (ModuleCat.{v} R) (functor R) := sorry
/- Proof strategy: characterize exact functors by short exact complexes. Use
`CharacterModule.exact_dual` for exactness of the underlying maps, together
with Mathlib's injectivity/surjectivity criteria for `CharacterModule.dual`. -/

/-- The noncommutative character-module functor to opposite-ring modules is
exact. -/
@[stacks 01DA "exactness of character duality over an arbitrary ring"]
theorem opExact (R : Type u) [Ring R] :
    exactFunctor (ModuleCat.{v} R)ᵒᵖ (ModuleCat.{v} Rᵐᵒᵖ)
      (opFunctor R) := sorry
/- Proof strategy: use the same underlying additive exactness as `exact`;
the opposite-ring scalar action changes only the bundled linear structure. -/

/-- Character duality sends a short exact complex to a short exact complex
with the arrows reversed. -/
@[stacks 01DA "character duality preserves short exactness contravariantly"]
theorem shortExact_map {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact) :
    (S.op.map (functor R)).ShortExact := sorry
/- Proof strategy: apply the short-exact characterization of `exact R` to
`S.op`, or prove the three underlying module conditions with
`CharacterModule.exact_dual`. -/

end CharacterModule
