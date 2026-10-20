module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Sequence
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SymmetricPower.Sequence
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open SheafOfModules.RingedSite

universe u

/- Lemma 17.21.4 (01CJ) (1): an exact pair of module sheaves with epimorphic final map induces
the canonical exact symmetric-power pair, again with epimorphic final map. -/
@[stacks 01CJ "(1), symmetric power"]
#check fun {X : RingedSpace.{u}} (S : ShortComplex X.Modules) (n : ℕ)
    (hS : S.Exact) [Epi S.g] =>
  SymmetricPower.sequence_exact_and_epi X.sheaf S n hS

/- Lemma 17.21.4 (01CJ) (2): the corresponding exterior-power pair is exact and ends in an
epimorphism. -/
@[stacks 01CJ "(2), exterior power"]
#check fun {X : RingedSpace.{u}} (S : ShortComplex X.Modules) (n : ℕ)
    (hS : S.Exact) [Epi S.g] =>
  ExteriorPower.sequence_exact_and_epi X.sheaf S n hS

/- The reusable data and the two atomic conclusions are also available independently. -/
#check fun {X : RingedSpace.{u}} (S : ShortComplex X.Modules) (n : ℕ) =>
  SymmetricPower.sequence X.sheaf S n

#check fun {X : RingedSpace.{u}} (S : ShortComplex X.Modules) (n : ℕ) =>
  ExteriorPower.sequence X.sheaf S n

/- The two sequence maps are exposed without unfolding the bundled short complex. -/
#check @SymmetricPower.sequence_f
#check @SymmetricPower.sequence_g
#check @ExteriorPower.sequence_f
#check @ExteriorPower.sequence_g

#check fun {X : RingedSpace.{u}} (S : ShortComplex X.Modules) (n : ℕ)
    (hS : S.Exact) [Epi S.g] =>
  SymmetricPower.sequence_exact X.sheaf S n hS

#check fun {X : RingedSpace.{u}} (S : ShortComplex X.Modules) (n : ℕ)
    (hS : S.Exact) [Epi S.g] =>
  ExteriorPower.sequence_exact X.sheaf S n hS

#check fun {X : RingedSpace.{u}} (S : ShortComplex X.Modules) (n : ℕ) [Epi S.g] =>
  SymmetricPower.sequence_epi X.sheaf S n

#check fun {X : RingedSpace.{u}} (S : ShortComplex X.Modules) (n : ℕ) [Epi S.g] =>
  ExteriorPower.sequence_epi X.sheaf S n
