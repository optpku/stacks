module

public import ReasLib.Algebra.WLocalHull.WLocalization

/-!
# W-localization of a commutative ring

The w-localization `A_w` of a commutative ring `A` is the filtered colimit of
the finite-stage algebras `A_E = Algebra.WLocalHull.stage A E` over the directed
poset of finite subsets `E : Finset A`.
-/

@[expose] public section

universe u

#check (Algebra.WLocalHull.wLocalization : ∀ (A : Type u) [CommRing A], Type u)

#check (Algebra.WLocalHull.stageMap :
  ∀ (A : Type u) [CommRing A] {E₁ E₂ : Finset A},
    E₁ ⊆ E₂ → Algebra.WLocalHull.stage A E₁ →+* Algebra.WLocalHull.stage A E₂)

#check (Algebra.WLocalHull.of :
  ∀ (A : Type u) [CommRing A] (E : Finset A),
    Algebra.WLocalHull.stage A E →+* Algebra.WLocalHull.wLocalization A)

#check (Algebra.WLocalHull.lift :
  ∀ (A : Type u) [CommRing A] {P : Type u} [CommRing P]
    (g : ∀ E, Algebra.WLocalHull.stage A E →+* P),
    (∀ E₁ E₂ h x, g E₂ (Algebra.WLocalHull.stageMap A h x) = g E₁ x) →
      Algebra.WLocalHull.wLocalization A →+* P)
