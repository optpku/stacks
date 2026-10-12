/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.AdicCompletion.Basic
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentCompletion

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {X : Scheme.{u}} [IsNoetherian X]
variable (I : Ideal A) [IsAdicComplete I A]
variable (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]

/-- Proposition 30.25.4: if `A` is Noetherian and `I`-adically complete and `f : X ⟶ Spec(A)` is
proper, then the coherent-completion functor `Coh(𝒪_X) ⥤ Coh(X, I 𝒪_X)` from (30.23.3.1)
is an equivalence. -/
@[stacks 088C, instance]
instance functor_isEquivalence_of_isProper :
    (functor ((idealSheafDataOfIdealOnSpec I).comap f)).IsEquivalence :=
  sorry

/-- Every coherent formal module along `I 𝒪_X` lies in the essential image of coherent
completion when `f` is proper over an `I`-adically complete Noetherian ring. -/
theorem mem_essImage_of_isProper
    (F : CoherentFormalModules X ((idealSheafDataOfIdealOnSpec I).comap f)) :
    (functor ((idealSheafDataOfIdealOnSpec I).comap f)).essImage F :=
  sorry

end AlgebraicGeometry.Scheme.CoherentCompletion
