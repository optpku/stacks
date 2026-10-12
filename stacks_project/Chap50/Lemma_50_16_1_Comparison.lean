/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.ExteriorPower.Pushforward

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

#check (AlgebraicGeometry.Scheme.RelativeDifferentials.pushforwardComparison :
  ∀ {X' X S' S : Scheme.{u}} {f : X' ⟶ X} {g : S' ⟶ S} {h : X ⟶ S} {h' : X' ⟶ S'},
    CommSq f h' h g → ∀ a : ℕ,
      (Λ[a] Ω[h.toShHom]) ⟶
        (RingedSpace.Hom.pushforward f.toShHom).obj (Λ[a] Ω[h'.toShHom]))
