/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Modification.Surface
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Domination

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsModification

/-- A modification of the spectrum of a two-dimensional local Noetherian normal ring,
with an explicit finite enumeration of its special-fibre components, is dominated by a
blowup admissible over the punctured spectrum. -/
theorem exists_admissibleBlowup_dominating
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [_root_.IsNormalRing A]
    (h_dimension : ringKrullDim A = 2) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsModification f] (r : ℕ)
    (C : Fin r ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint A))) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ Spec (.of A)) (g : X' ⟶ X),
      IsAdmissibleBlowup (PuncturedSpectrum.puncturedOpen A) b ∧ g ≫ f = b := sorry

end AlgebraicGeometry.IsModification
