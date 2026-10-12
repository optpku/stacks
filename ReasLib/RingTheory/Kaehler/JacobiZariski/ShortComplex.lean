/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import ReasLib.RingTheory.Kaehler.JacobiZariski
import Mathlib.Tactic.CrossRefAttribute

/-!
# The Kähler transitivity short complex

For a tower of commutative algebras `R → S → T`, the canonical maps

`T ⊗[S] Ω[S⁄R] ⟶ Ω[T⁄R] ⟶ Ω[T⁄S]`

form the transitivity short complex.  The underlying maps and the categorical
packaging live here; exactness and short-exactness are separate statements so
that downstream users can consume the smallest useful API.

The `ModuleCat` packaging uses one universe for `R`, `S`, and `T`.  The map
theorems in `ReasLib.RingTheory.Kaehler.JacobiZariski` remain universe-polymorphic;
this uniformity is only the unavoidable boundary imposed by `ModuleCat`.

@stack 04B2
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

namespace KaehlerDifferential.Transitivity

variable {R S T : Type u}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- The two canonical Kähler transitivity maps compose to zero. -/
@[stacks 04B2 "Kähler transitivity composition"]
theorem map_comp_mapBaseChange :
    (KaehlerDifferential.map R S T T).comp
        (KaehlerDifferential.mapBaseChange R S T) = 0 := sorry

/-- The canonical `ModuleCat` short complex attached to Kähler transitivity. -/
@[stacks 04B2 "Kähler transitivity short complex"]
noncomputable def complex : ShortComplex (ModuleCat.{u} T) :=
  ShortComplex.moduleCatMk
    (KaehlerDifferential.mapBaseChange R S T) (KaehlerDifferential.map R S T T)
    (map_comp_mapBaseChange (R := R) (S := S) (T := T))

/-- The Kähler transitivity short complex is exact for every commutative algebra tower. -/
@[stacks 00RS "Jacobi-Zariski exactness for Kähler differentials"]
theorem exact :
    (complex (R := R) (S := S) (T := T)).Exact := sorry

/-- For the transitivity complex, short exactness is equivalent to injectivity of the
base-change map; exactness and surjectivity of the terminal map are built into the canonical API. -/
@[stacks 04B2 "short exactness criterion"]
theorem shortExact_iff_mapBaseChange_injective :
    (complex (R := R) (S := S) (T := T)).ShortExact ↔
      Function.Injective (KaehlerDifferential.mapBaseChange R S T) := sorry

/-- Formal smoothness of `S → T` makes the Kähler transitivity complex short exact. -/
@[stacks 04B2 "formally smooth Kähler transitivity"]
theorem shortExact_of_formallySmooth [Algebra.FormallySmooth S T] :
    (complex (R := R) (S := S) (T := T)).ShortExact := sorry

/-- Lemma 10.139.1 (Tag 04B2): smoothness of `S → T` makes the Kähler transitivity complex
short exact over `R`. -/
@[stacks 04B2]
theorem shortExact_of_smooth [Algebra.Smooth S T] :
    (complex (R := R) (S := S) (T := T)).ShortExact := sorry

end KaehlerDifferential.Transitivity
