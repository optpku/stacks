/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.StrictHenselization
public import ReasLib.RingTheory.RingHom.WeaklyEtale

@[expose] public section

/-!
# Weakly Étale Maps and Strict Henselizations
-/

universe u v

namespace RingHom

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

/-- A local ring homomorphism induces isomorphisms on strict henselizations when every
local comparison commuting with the two structural maps is bijective. -/
def IsIsoOnStrictHenselizations (φ : R →+* S) [IsLocalHom φ] : Prop :=
  ∀ {Rsh : Type u} {Ssh : Type v}
    [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]
    [CommRing Ssh] [Algebra S Ssh] [IsStrictHenselizationOf S Ssh]
    (comparison : Rsh →+* Ssh), IsLocalHom comparison →
      comparison.comp (algebraMap R Rsh) = (algebraMap S Ssh).comp φ →
        Function.Bijective comparison

namespace IsIsoOnStrictHenselizations

/-- A compatible local comparison of strict henselizations is bijective when the base map
induces isomorphisms on strict henselizations. -/
theorem bijective {φ : R →+* S} [IsLocalHom φ]
    (hφ : φ.IsIsoOnStrictHenselizations)
    {Rsh : Type u} {Ssh : Type v}
    [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]
    [CommRing Ssh] [Algebra S Ssh] [IsStrictHenselizationOf S Ssh]
    (comparison : Rsh →+* Ssh) (hcomparisonLocal : IsLocalHom comparison)
    (hcomparison : comparison.comp (algebraMap R Rsh) =
      (algebraMap S Ssh).comp φ) : Function.Bijective comparison := sorry

end IsIsoOnStrictHenselizations

namespace WeaklyEtale

/-- A local ring homomorphism is weakly étale exactly when it induces isomorphisms on
strict henselizations. -/
theorem iff_isIsoOnStrictHenselizations (φ : R →+* S) [IsLocalHom φ] :
    φ.WeaklyEtale ↔ φ.IsIsoOnStrictHenselizations := sorry

end WeaklyEtale

end RingHom
