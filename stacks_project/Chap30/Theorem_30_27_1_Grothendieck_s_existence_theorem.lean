module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.AdicCompletion.Basic
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.ProperSupport
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {X : Scheme.{u}} [IsNoetherian X]
variable (I : Ideal A) [IsAdicComplete I A]
variable (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f] [Scheme.Hom.FiniteType f]

/-- Theorem 30.27.1 (Grothendieck's existence theorem): if `A` is Noetherian and `I`-adically
complete and `f : X ⟶ Spec(A)` is separated of finite type, then the completion functor
from coherent `𝒪_X`-modules with support proper over `Spec(A)` to coherent formal `I 𝒪_X`-modules
with first-stage support proper over `Spec(A)` is an equivalence. -/
@[stacks 088E, instance]
instance instIsEquivalence_coherentProperSupportCompletionFunctor :
    (coherentProperSupportCompletionFunctor :
      CoherentProperSupportOver f ⥤
        CoherentFormalProperSupportOver f ((idealSheafDataOfIdealOnSpec I).comap f)).IsEquivalence :=
  sorry

/-- Every coherent formal module along `I 𝒪_X` whose first stage has support proper over `Spec(A)`
lies in the essential image of proper-support coherent completion when `f` is separated of finite
type over an `I`-adically complete Noetherian ring. -/
theorem mem_essImage_coherentProperSupportCompletionFunctor
    (F : CoherentFormalProperSupportOver f ((idealSheafDataOfIdealOnSpec I).comap f)) :
    (coherentProperSupportCompletionFunctor :
      CoherentProperSupportOver f ⥤
        CoherentFormalProperSupportOver f ((idealSheafDataOfIdealOnSpec I).comap f)).essImage F :=
  sorry

end AlgebraicGeometry.Scheme.Modules
