/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Affine
public import ReasLib.RingTheory.PicardGroup.Ideal
public import ReasLib.RingTheory.PicardGroup.Invertible
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u v

section Affine

variable {R : CommRingCat.{u}} (M : ModuleCat R)

/- Exercise 111.40.3 (1): an invertible 𝒪_X-module on an affine scheme Spec A corresponds to an
A-module which is finite, projective, and locally free of rank 1, hence flat and finitely
presented. -/
@[stacks 02AF] #check
  (AlgebraicGeometry.Scheme.Modules.tilde_invertible_iff_module_invertible M :
    AlgebraicGeometry.Scheme.Modules.Invertible (AlgebraicGeometry.tilde M) ↔
      Module.Invertible R M)

variable [Module.Invertible R M]

#check (AlgebraicGeometry.Scheme.Modules.instInvertibleTilde M)

variable {L : (Spec R).Modules} [AlgebraicGeometry.Scheme.Modules.Invertible L]

#check (AlgebraicGeometry.Scheme.Modules.instInvertibleModuleSpecΓ L :
  Module.Invertible R (AlgebraicGeometry.moduleSpecΓFunctor.obj L))
#check (AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent L)

end Affine

section AlgebraicConsequences

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Invertible R M]

#synth Module.Finite R M
#synth Module.Projective R M
#synth Module.FiniteLocallyFreeOfRank R M 1
#synth Module.Flat R M
#check (Module.finitePresentation_of_projective R M : Module.FinitePresentation R M)

#check (Module.Invertible.iff_finiteLocallyFreeOfRank_one (R := R) (M := M) :
  Module.Invertible R M ↔ Module.FiniteLocallyFreeOfRank R M 1)

end AlgebraicConsequences

section IdealRealization

variable {R : Type u} {M : Type v} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
  [Module.Invertible R M]

/- Exercise 111.40.3 (2): if A is a domain and M is such a module, then M is isomorphic as an
A-module to an ideal I ⊆ A such that I A_p is principal for every prime p. -/
@[stacks 02AF] #check
  (Module.Invertible.exists_linearEquiv_ideal_locallyPrincipal R M :
    ∃ I : Ideal R, Nonempty (M ≃ₗ[R] I) ∧
      ∀ p : PrimeSpectrum R, (I.localizationAtPrime p).IsPrincipal)

end IdealRealization
