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

/-- The coherent-completion functor along `I 𝒪_X` is fully faithful when `f` is proper
over an `I`-adically complete Noetherian ring. -/
@[stacks 0883]
theorem fullyFaithful_of_isProper :
    Nonempty (functor ((idealSheafDataOfIdealOnSpec I).comap f)).FullyFaithful :=
  sorry

/-- The coherent-completion functor along `I 𝒪_X` induces a bijection on morphisms of
coherent modules when `f` is proper over an `I`-adically complete Noetherian ring. -/
theorem map_bijective_of_isProper (F G : RingedSpace.Coh X.toRingedSpace) :
    Function.Bijective
      (fun φ : F ⟶ G ↦ (functor ((idealSheafDataOfIdealOnSpec I).comap f)).map φ) :=
  sorry

/-- The coherent-completion functor along `I 𝒪_X` is full when `f` is proper over an
`I`-adically complete Noetherian ring. -/
instance functor_full_of_isProper :
    (functor ((idealSheafDataOfIdealOnSpec I).comap f)).Full :=
  sorry

/-- The coherent-completion functor along `I 𝒪_X` is faithful when `f` is proper over an
`I`-adically complete Noetherian ring. -/
instance functor_faithful_of_isProper :
    (functor ((idealSheafDataOfIdealOnSpec I).comap f)).Faithful :=
  sorry

end AlgebraicGeometry.Scheme.CoherentCompletion
