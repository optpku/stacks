module

public import ReasLib.RingTheory.Ideal.Radical.FiniteGeneration
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Noetherian prime spectra and finite generation up to radical

@stack 0G2Z
-/

@[expose] public section

universe u

open TopologicalSpace

namespace PrimeSpectrum

variable {R : Type u} [CommSemiring R]

/-- In a Noetherian prime spectrum, every ideal is finitely generated up to radical. -/
@[stacks 0G2Z "finite generation up to radical from a Noetherian spectrum"]
theorem fgUpToRadical_of_noetherianSpace
    (hX : NoetherianSpace (PrimeSpectrum R)) (I : Ideal R) :
    I.FGUpToRadical := by
  have hcompact : IsCompact ((zeroLocus (I : Set R))ᶜ) :=
    (noetherianSpace_iff_isCompact (α := PrimeSpectrum R)).mp hX _
  obtain ⟨J, hJfg, hJopen⟩ :=
    (isCompact_isOpen_iff_ideal :
      IsCompact ((zeroLocus (I : Set R))ᶜ) ∧ IsOpen ((zeroLocus (I : Set R))ᶜ) ↔
        ∃ J : Ideal R, J.FG ∧ (zeroLocus (J : Set R))ᶜ = (zeroLocus (I : Set R))ᶜ).mp
      ⟨hcompact, (isClosed_zeroLocus (I : Set R)).isOpen_compl⟩
  refine ⟨J, hJfg, ?_⟩
  have hzero : zeroLocus (J : Set R) = zeroLocus (I : Set R) := by
    simpa using congrArg (fun s : Set (PrimeSpectrum R) ↦ sᶜ) hJopen
  exact (zeroLocus_eq_iff.mp hzero).symm

/-- If every ideal is finitely generated up to radical, then the prime spectrum is Noetherian. -/
@[stacks 0G2Z "Noetherian spectrum from finite generation up to radical"]
theorem noetherianSpace_of_forall_fgUpToRadical
    (hI : ∀ I : Ideal R, I.FGUpToRadical) :
    NoetherianSpace (PrimeSpectrum R) := by
  refine (noetherianSpace_iff_opens (α := PrimeSpectrum R)).2 ?_
  intro U
  obtain ⟨I, hIeq⟩ :=
    (isClosed_iff_zeroLocus_ideal ((U : Set (PrimeSpectrum R))ᶜ)).mp U.isOpen.isClosed_compl
  rcases hI I with ⟨J, hJfg, hJrad⟩
  have hzero : zeroLocus (J : Set R) = zeroLocus (I : Set R) :=
    zeroLocus_eq_iff.mpr hJrad.symm
  have hU0 : (zeroLocus (I : Set R))ᶜ = (U : Set (PrimeSpectrum R)) := by
    simpa using (congrArg (fun s : Set (PrimeSpectrum R) ↦ sᶜ) hIeq).symm
  have hU : (zeroLocus (J : Set R))ᶜ = (U : Set (PrimeSpectrum R)) := by
    rw [hzero]
    exact hU0
  exact
    (isCompact_isOpen_iff_ideal :
      IsCompact (U : Set (PrimeSpectrum R)) ∧ IsOpen (U : Set (PrimeSpectrum R)) ↔
        ∃ I : Ideal R, I.FG ∧ (zeroLocus (I : Set R))ᶜ = (U : Set (PrimeSpectrum R))).mpr
      ⟨J, hJfg, hU⟩ |>.1

/-- The prime spectrum is Noetherian exactly when every ideal is finitely generated up to
radical. -/
@[stacks 0G2Z "Noetherian spectrum criterion for all ideals"]
theorem noetherianSpace_iff_forall_fgUpToRadical :
    NoetherianSpace (PrimeSpectrum R) ↔ ∀ I : Ideal R, I.FGUpToRadical :=
  ⟨fun h I ↦ fgUpToRadical_of_noetherianSpace h I,
    noetherianSpace_of_forall_fgUpToRadical⟩

/-- The prime spectrum is Noetherian exactly when every radical ideal is finitely generated up to
radical. -/
@[stacks 0G2Z "Noetherian spectrum criterion for radical ideals"]
theorem noetherianSpace_iff_forall_isRadical_fgUpToRadical :
    NoetherianSpace (PrimeSpectrum R) ↔
      ∀ I : Ideal R, I.IsRadical → I.FGUpToRadical := by
  constructor
  · intro hX I _
    exact fgUpToRadical_of_noetherianSpace hX I
  · intro hrad
    apply noetherianSpace_of_forall_fgUpToRadical
    intro I
    rw [← Ideal.radical_fgUpToRadical I]
    exact hrad I.radical (Ideal.radical_isRadical I)

/-- The prime spectrum is Noetherian exactly when every prime ideal is finitely generated up to
radical. -/
@[stacks 0G2Z "Noetherian spectrum criterion for prime ideals"]
theorem noetherianSpace_iff_forall_isPrime_fgUpToRadical :
    NoetherianSpace (PrimeSpectrum R) ↔
      ∀ P : Ideal R, P.IsPrime → P.FGUpToRadical := by
  constructor
  · intro hX P _
    exact fgUpToRadical_of_noetherianSpace hX P
  · intro hprime
    apply noetherianSpace_of_forall_fgUpToRadical
    exact Ideal.isOka_fgUpToRadical.forall_of_forall_prime'
      (fun C _ hC I hI hSup ↦
        Ideal.exists_mem_fgUpToRadical_of_sSup hC ⟨I, hI⟩ hSup)
      hprime

end PrimeSpectrum
