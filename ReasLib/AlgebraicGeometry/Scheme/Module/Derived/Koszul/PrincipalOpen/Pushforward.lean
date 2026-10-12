/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Koszul.PrincipalOpen.Factorization
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Pushforward.Derived
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Affine
public import ReasLib.CategoryTheory.DerivedCategory.Ext

@[expose] public section

open CategoryTheory
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

open RingedSpace.ModuleDerived.Koszul
open RingedSpace.OpenSubspace.Pushforward
open KoszulComplex.PowerTower
open PrincipalOpenCech

/-- For an affine scheme and a finite union of principal opens, the derived
restriction-pushforward unit is invertible exactly when all morphisms from integer shifts of
the associated stage-zero Koszul object vanish. -/
theorem openUnit_isIso_iff_koszulHom_subsingleton
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
    (E : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent
      (Spec (CommRingCat.of A))) :
    IsIso
        ((derivedAdjunction (Spec (CommRingCat.of A)).toRingedSpace
          (openSubset f)).unit.app E.obj) ↔
      ∀ n : ℤ,
        Subsingleton
          (((affineDerivedTilde A).obj (derivedStage f 0))⟦n⟧ ⟶ E.obj) := sorry

/-- For an affine scheme and a finite union of principal opens, the derived
restriction-pushforward unit is invertible exactly when every derived extension group from the
associated stage-zero Koszul object is subsingleton. -/
theorem openUnit_isIso_iff_koszulExt_subsingleton
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
    (E : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent
      (Spec (CommRingCat.of A))) :
    IsIso
        ((derivedAdjunction (Spec (CommRingCat.of A)).toRingedSpace
          (openSubset f)).unit.app E.obj) ↔
      ∀ n : ℤ,
        Subsingleton
          (Ext⁽n⁾((affineDerivedTilde A).obj (derivedStage f 0), E.obj)) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
