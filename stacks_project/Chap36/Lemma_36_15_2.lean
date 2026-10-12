/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Koszul.PrincipalOpen.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped DerivedExt

noncomputable section

universe u

/- Lemma 36.15.2: for `X = Spec(A)` and `U = PrincipalOpenCech.openSubset f`, the canonical
map `E.obj ⟶ Rj_*(E.obj|_U)` is an isomorphism if and only if every morphism from an integer
shift of the affine stage-zero Koszul object to `E.obj` vanishes. -/
@[stacks 09IR] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.openUnit_isIso_iff_koszulHom_subsingleton :
    ∀ {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
      (E : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent
        (AlgebraicGeometry.Spec (CommRingCat.of A))),
      IsIso
          ((AlgebraicGeometry.RingedSpace.OpenSubspace.Pushforward.derivedAdjunction
            (AlgebraicGeometry.Spec (CommRingCat.of A)).toRingedSpace
            (AlgebraicGeometry.Scheme.PrincipalOpenCech.openSubset f)).unit.app E.obj) ↔
        ∀ n : ℤ,
          Subsingleton
            (((AlgebraicGeometry.RingedSpace.ModuleDerived.Koszul.affineDerivedTilde A).obj
              (KoszulComplex.PowerTower.derivedStage f 0))⟦n⟧ ⟶ E.obj))

#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.openUnit_isIso_iff_koszulExt_subsingleton :
    ∀ {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
      (E : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent
        (AlgebraicGeometry.Spec (CommRingCat.of A))),
      IsIso
          ((AlgebraicGeometry.RingedSpace.OpenSubspace.Pushforward.derivedAdjunction
            (AlgebraicGeometry.Spec (CommRingCat.of A)).toRingedSpace
            (AlgebraicGeometry.Scheme.PrincipalOpenCech.openSubset f)).unit.app E.obj) ↔
        ∀ n : ℤ,
          Subsingleton
            (Ext⁽n⁾(
              (AlgebraicGeometry.RingedSpace.ModuleDerived.Koszul.affineDerivedTilde A).obj
                (KoszulComplex.PowerTower.derivedStage f 0), E.obj)))

end
