module

public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Pushforward.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Koszul.PrincipalOpen.Factorization
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn

@[expose] public section

open CategoryTheory
open DerivedCategory.TStructure
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

open RingedSpace.ModuleDerived.Koszul
open RingedSpace.OpenSubspace.Pushforward
open KoszulComplex.PowerTower
open PrincipalOpenCech

/-- Vanishing of the Ext groups from the stage-zero affine Koszul object in degrees at
least `a` makes the degree-`a` lower truncation of the principal-open adjunction unit an
isomorphism. -/
theorem truncGEOpenUnit_isIso_of_extSubsingleton {A : Type u} [CommRing A] {r : ℕ}
    (f : Fin r → A)
    (E : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent (Spec (CommRingCat.of A)))
    (a : ℤ)
    (h_ext : ∀ n : ℤ, a ≤ n →
      Subsingleton
        (Ext⁽n⁾(
          (affineDerivedTilde A).obj (derivedStage f 0), E.obj))) :
    IsIso
      ((t.truncGE a).map
        ((derivedAdjunction (Spec (CommRingCat.of A)).toRingedSpace
          (openSubset f)).unit.app E.obj)) := sorry

/-- If the degree-`a` lower truncation of the principal-open adjunction unit is an
isomorphism, then the Ext groups from the stage-zero affine Koszul object vanish in degrees
at least `a + 1`. -/
theorem extSubsingleton_succ_of_truncGEOpenUnit_isIso
    {A : Type u} [CommRing A] {r : ℕ}
    (f : Fin r → A)
    (E : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent (Spec (CommRingCat.of A)))
    (a : ℤ)
    (h_iso : IsIso
      ((t.truncGE a).map
        ((derivedAdjunction (Spec (CommRingCat.of A)).toRingedSpace
          (openSubset f)).unit.app E.obj))) :
    ∀ n : ℤ, a + 1 ≤ n →
      Subsingleton
        (Ext⁽n⁾(
          (affineDerivedTilde A).obj (derivedStage f 0), E.obj)) := sorry

/-- Vanishing of the Ext groups from the stage-zero affine Koszul object in degrees at
most `a` makes the degree-`a` upper truncation of the principal-open adjunction unit an
isomorphism. -/
theorem truncLEOpenUnit_isIso_of_extSubsingleton {A : Type u} [CommRing A] {r : ℕ}
    (f : Fin r → A)
    (E : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent (Spec (CommRingCat.of A)))
    (a : ℤ)
    (h_ext : ∀ n : ℤ, n ≤ a →
      Subsingleton
        (Ext⁽n⁾(
          (affineDerivedTilde A).obj (derivedStage f 0), E.obj))) :
    IsIso
      ((t.truncLE a).map
        ((derivedAdjunction (Spec (CommRingCat.of A)).toRingedSpace
          (openSubset f)).unit.app E.obj)) := sorry

/-- If the degree-`a` upper truncation of the principal-open adjunction unit is an
isomorphism, then the Ext groups from the stage-zero affine Koszul object vanish in degrees
at most `a - 1`. -/
theorem extSubsingleton_pred_of_truncLEOpenUnit_isIso
    {A : Type u} [CommRing A] {r : ℕ}
    (f : Fin r → A)
    (E : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent (Spec (CommRingCat.of A)))
    (a : ℤ)
    (h_iso : IsIso
      ((t.truncLE a).map
        ((derivedAdjunction (Spec (CommRingCat.of A)).toRingedSpace
          (openSubset f)).unit.app E.obj))) :
    ∀ n : ℤ, n ≤ a - 1 →
      Subsingleton
        (Ext⁽n⁾(
          (affineDerivedTilde A).obj (derivedStage f 0), E.obj)) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
