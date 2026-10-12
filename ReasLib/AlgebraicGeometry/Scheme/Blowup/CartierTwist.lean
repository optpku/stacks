/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.TwistingSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.CartierTwist
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open SheafOfModules.RingedSite.IdealSheaf

noncomputable section

universe u

namespace AlgebraicGeometry.IsBlowup

variable {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
variable (p : X ⟶ Spec (CommRingCat.of A))
  [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)]

/-- Every integral power of the exceptional twisting sheaf is invertible. -/
instance twistingSheaf_isInvertible (q : ℤ) :
    Scheme.Modules.Invertible (twistingSheaf I p q) := sorry

/-- The canonical map from a coherent module to its negative exceptional twist. -/
def canonicalTwistMap (F : X.Modules) (c : ℕ) :
    F ⟶ F ⊗ (twistingSheaf I p (-(c : ℤ))) :=
  Scheme.Modules.CartierTwist.map (exceptionalIdeal I p) F c

/-- Coherent modules are annihilated by an exceptional ideal power exactly when
the canonical map to the corresponding negative twist vanishes. -/
theorem isAnnihilated_exceptionalDivisorPow_iff_canonicalTwistMap_eq_zero
    (c : ℕ) (F : X.Modules) [F.IsCoherent] :
    IsAnnihilated
        (((Scheme.idealSheafDataOfIdealOnSpec I).comap p) ^ c).toSubobject F ↔
      canonicalTwistMap I p F c = 0 :=
  Scheme.Modules.CartierTwist.annihilated_iff_map (exceptionalIdeal I p) F c

end AlgebraicGeometry.IsBlowup
