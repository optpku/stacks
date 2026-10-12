/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Pushforward
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 50.3.2: If `p : X ⟶ S` is quasi-compact and quasi-separated, then the derived
pushforward of the relative de Rham complex has quasicoherent cohomology on `S`. -/
@[stacks 0FLX] #check
  (AlgebraicGeometry.Scheme.DeRham.pushforwardDerivedComplex_isQuasicoherent :
    ∀ {X S : Scheme.{u}} (p : X ⟶ S) [QuasiCompact p] [QuasiSeparated p],
      Scheme.derivedQuasiCoherentModuleProperty S
        ((RingedSpace.moduleDerivedPushforward
          (Scheme.ModuleCech.relativeSpaceMap p.toLRSHom.toShHom)).obj
          ((CochainComplex.Nat.toDerived
            (Scheme.ModuleCech.relativeSpace p.toLRSHom.toShHom).Modules).obj
            (RingedSpace.DeRham.complex p.toLRSHom.toShHom))))
