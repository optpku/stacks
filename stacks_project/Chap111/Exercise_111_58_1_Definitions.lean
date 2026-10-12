/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReasLib.RingTheory.Catenary.Basic
public import ReasLib.RingTheory.CohenMacaulay.Ring
import StacksCheckRecall

@[expose] public section

universe u v

variable {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
variable (M : Type v) [AddCommGroup M] [Module R M]

/- Exercise 111.58.1 (Definitions): `R` is catenary when its prime spectrum is catenary. -/
@[stacks 0D5G] #check (IsCatenaryRing R : Prop)

#check (isCatenaryRing_iff_catenarySpace_primeSpectrum :
  IsCatenaryRing R ↔ TopologicalSpace.CatenarySpace (PrimeSpectrum R))

/- The local ring of `R` at a prime `p` is its localization at `p.primeCompl`. -/
#check (Localization.AtPrime p : Type u)

#check (Localization.AtPrime.isLocalRing p : IsLocalRing (Localization.AtPrime p))

/- A finite `R`-module is finitely generated, not necessarily finite as a set. -/
#check (Module.Finite R M : Prop)

#check (Module.finite_def : Module.Finite R M ↔ (⊤ : Submodule R M).FG)

/- A finitely presented `R`-module has finitely many generators and relations. -/
#check (Module.FinitePresentation R M : Prop)

/- `R` is regular when it is Noetherian and its prime localizations are regular local rings. -/
#check (IsRegularRing R : Prop)

section
variable [IsNoetherianRing R]

#check (isRegularRing_iff :
  IsRegularRing R ↔
    ∀ (q : Ideal R) [q.IsPrime], IsRegularLocalRing (Localization.AtPrime q))

end

/- `R` is Cohen–Macaulay when it is Noetherian and its prime localizations are Cohen–Macaulay. -/
#check (CohenMacaulayRing R : Prop)

#check (CohenMacaulayRing.localizedRing_cohenMacaulay R :
  ∀ (q : PrimeSpectrum R) [CohenMacaulayRing R],
    Module.CohenMacaulay (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal))
