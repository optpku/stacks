/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.IteratedRelative.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {p : ℕ} [Fact p.Prime]
variable {U X : Scheme.{u}} (f : U ⟶ X)
variable [Scheme.IsCharP X p]

/-- The structure morphism of a Frobenius-power twist of an étale morphism is
étale. -/
instance pPowerTwist_etale [Etale f] (n : ℕ) :
    Etale (pPowerTwist (p := p) f n).hom :=
  inferInstanceAs (Etale (pullback.snd f (absoluteFrobeniusPow p X n)))

/-- Relative Frobenius of a Frobenius-power twist of an étale morphism is an
isomorphism. -/
instance relativeFrobenius_pPowerTwist_isIso [Etale f] (n : ℕ) :
    IsIso (Hom.relativeFrobenius (p := p) (pPowerTwist (p := p) f n).hom) :=
  Hom.relativeFrobenius_isIso_of_etale (pPowerTwist (p := p) f n).hom

/-- Inverse of the underlying scheme morphism of iterated relative Frobenius of
an étale morphism, obtained by reversing successive relative-Frobenius steps. -/
def iteratedRelativeFrobeniusLeftInv [Etale f] :
    (n : ℕ) → (pPowerTwist (p := p) f n).left ⟶ U
  | 0 => pullback.fst f (absoluteFrobeniusPow p X 0)
  | n + 1 =>
      (pPowerTwistSuccIso (p := p) f n).inv.left ≫
        (pullback.congrHom rfl
            (absoluteFrobenius_eq_absoluteFrobeniusPow_one p X)).inv ≫
          CategoryTheory.inv
              (Hom.relativeFrobenius (p := p) (pPowerTwist (p := p) f n).hom) ≫
            iteratedRelativeFrobeniusLeftInv n

/-- Iterated relative Frobenius followed by its recursive inverse is the identity. -/
theorem iteratedRelativeFrobeniusLeftIso_hom_inv_id [Etale f] (n : ℕ) :
    (iteratedRelativeFrobenius (p := p) f n).left ≫
        iteratedRelativeFrobeniusLeftInv (p := p) f n = 𝟙 U := sorry

/-- The recursive inverse followed by iterated relative Frobenius is the identity. -/
theorem iteratedRelativeFrobeniusLeftIso_inv_hom_id [Etale f] (n : ℕ) :
    iteratedRelativeFrobeniusLeftInv (p := p) f n ≫
        (iteratedRelativeFrobenius (p := p) f n).left =
      𝟙 (pPowerTwist (p := p) f n).left := sorry

/-- The underlying scheme morphism of iterated relative Frobenius of an étale
morphism, as a scheme isomorphism. -/
def iteratedRelativeFrobeniusLeftIso [Etale f] (n : ℕ) :
    U ≅ (pPowerTwist (p := p) f n).left where
  hom := (iteratedRelativeFrobenius (p := p) f n).left
  inv := iteratedRelativeFrobeniusLeftInv (p := p) f n
  hom_inv_id := iteratedRelativeFrobeniusLeftIso_hom_inv_id (p := p) f n
  inv_hom_id := iteratedRelativeFrobeniusLeftIso_inv_hom_id (p := p) f n

end AlgebraicGeometry.Scheme
