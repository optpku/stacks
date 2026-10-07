module

public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.Order.WithBotTop
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension.KrullDimension
public import stacks_project.Chap51.Lemma_51_4_1
public import stacks_project.Chap51.Lemma_51_4_6
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.DerivedCategory
open CategoryTheory.DerivedCategory.LocalCohomology

universe u

namespace Ideal.LocalCohomology

/- Lemma 51.4.7 (1): local cohomology with support in `V(I)` of an arbitrary finite module
vanishes in every degree strictly above the Krull dimension of its support. -/
@[stacks 0DXC]
 #check
  (Ideal.LocalCohomology.isZero_above_supportDim :
    ∀ {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
      [Module.Finite A M] (I : Ideal A) (hI : I.FG)
      (RΓ : DerivedCategory (ModuleCat A) ⥤ DerivedCategory.IdealPowerTorsion I)
      (hRΓ : DerivedCategory.IdealPowerTorsion.inclusion I ⊣ RΓ) (i : ℤ)
      (hi : WithBot.map (WithTop.map Int.ofNat) (Module.supportDim A M) < (i : EInt)),
      IsZero (supportedCohomology I RΓ (ModuleCat.of A M) i))

/- Lemma 51.4.7 (2): for a nontrivial ring, the local-cohomological dimension of a finitely
generated ideal is at most the Krull dimension of the ambient ring. The all-ring bound is
truncated below by `-1`, since the zero ring has Krull dimension `-∞` in the right-hand side
convention while local-cohomological dimension is bounded below by `-1`. -/
@[stacks 0DXC]
 #check
  (Ideal.LocalCohomology.dimension_le_ringKrullDim :
    ∀ {A : Type u} [CommRing A] [Nontrivial A] (I : Ideal A) (hI : I.FG),
      (dimension I hI : EInt) ≤
        WithBot.map (WithTop.map Int.ofNat) (ringKrullDim A))

/- The unrestricted all-ring form of the dimension estimate. -/
#check
  (Ideal.LocalCohomology.dimension_le_max_ringKrullDim :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG),
      (dimension I hI : EInt) ≤
        max ((-1 : ℤ) : EInt) (WithBot.map (WithTop.map Int.ofNat) (ringKrullDim A)))

end Ideal.LocalCohomology
