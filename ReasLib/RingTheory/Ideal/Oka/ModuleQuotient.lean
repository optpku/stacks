module

public import ReasLib.RingTheory.Ideal.Quotient.Colon
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.RingTheory.Ideal.Oka
import Mathlib.Tactic.CrossRefAttribute

/-!
# Oka families from module quotients

An extension-closed property of modules that contains zero produces an Oka family by evaluating
the property on ideal quotients.  Closure under isomorphisms is a consequence of these two
hypotheses, so it is deliberately absent from the public signature.

@stack 0G1N
-/

@[expose] public section

open CategoryTheory

universe u

namespace Ideal.IsOka

variable {A : Type u} [CommRing A]

/-- Example 10.28.7 (Tag 0G1N) (2): a property of `A`-modules that is closed under extensions and
holds for zero defines an Oka family through ideal quotients. -/
@[stacks 0G1N "(2)"]
theorem ofQuotientModuleProperty (P : ObjectProperty (ModuleCat.{u} A))
    [P.IsClosedUnderExtensions] [P.ContainsZero] :
    Ideal.IsOka (fun I : Ideal A ↦ P (ModuleCat.of A (A ⧸ I))) := sorry

end Ideal.IsOka
