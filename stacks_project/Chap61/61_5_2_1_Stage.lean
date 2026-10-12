/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.WLocalHull.Stage

/-!
# Finite vanishing-pattern stages

The finite-stage algebra attached to `E : Finset A` is the product of
specializing localizations over vanishing patterns of `E`.
-/

@[expose] public section

universe u

#check (Algebra.WLocalHull.Pattern :
  ∀ (ring : Type u), Finset ring → Type u)

#check (Algebra.WLocalHull.Pattern.elem :
  ∀ (ring : Type u) [CommRing ring] {subset : Finset ring},
    Algebra.WLocalHull.Pattern ring subset → ring)

#check (Algebra.WLocalHull.Pattern.span :
  ∀ (ring : Type u) [CommRing ring] {subset : Finset ring},
    Algebra.WLocalHull.Pattern ring subset → Ideal ring)

#check (Algebra.WLocalHull.stage :
  ∀ (ring : Type u) [CommRing ring], Finset ring → Type u)

#check (Algebra.WLocalHull.stage.eval :
  ∀ (ring : Type u) [CommRing ring] {subset : Finset ring}
    (pattern : Algebra.WLocalHull.Pattern ring subset),
      Algebra.WLocalHull.stage ring subset →+*
        Algebra.WLocalHull.specializingLocalization ring pattern.elem pattern.span)
