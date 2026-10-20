/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.CharP.Frobenius
public import ReasLib.AlgebraicGeometry.Scheme.Characteristic.Prime

/-!
# Absolute Frobenius of schemes

This leaf owns the absolute Frobenius of a scheme whose structure-sheaf
sections have characteristic `p`, together with its sectionwise computation
and naturality square.
-/

@[expose] public section

open CategoryTheory Opposite TopCat
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry
namespace Scheme

/-- The sectionwise Frobenius endomorphism of the structure presheaf on a scheme in
characteristic `p`. -/
theorem absoluteFrobeniusNatTrans_naturality (p : ℕ) [Fact p.Prime] (X : Scheme.{u})
    [IsCharP X p] {U V : X.Opensᵒᵖ} (i : U ⟶ V) :
    X.presheaf.map i ≫ CommRingCat.ofHom
        (RingHom.frobeniusOfPrime p (IsCharP.cast_eq_zero (X := X) (unop V))) =
      CommRingCat.ofHom
          (RingHom.frobeniusOfPrime p (IsCharP.cast_eq_zero (X := X) (unop U))) ≫
        X.presheaf.map i := sorry

/-- The natural endomorphism of the structure presheaf induced sectionwise by the `p`-th power
map. -/
abbrev absoluteFrobeniusNatTrans (p : ℕ) [Fact p.Prime] (X : Scheme.{u})
    [IsCharP X p] :
    X.presheaf ⟶ X.presheaf where
  app U := CommRingCat.ofHom
    (RingHom.frobeniusOfPrime p (IsCharP.cast_eq_zero (X := X) (unop U)))
  naturality {_ _} i :=
    absoluteFrobeniusNatTrans_naturality p X i

/-- The underlying morphism of sheafed spaces for the absolute Frobenius on a scheme in
characteristic `p`. -/
abbrev absoluteFrobeniusToSheafedSpaceHom (p : ℕ) [Fact p.Prime] (X : Scheme.{u})
    [IsCharP X p] :
    X.toSheafedSpace ⟶ X.toSheafedSpace :=
  InducedCategory.homMk
    { base := 𝟙 (X : TopCat)
      c := absoluteFrobeniusNatTrans p X ≫
        eqToHom (Presheaf.Pushforward.id_eq X.presheaf).symm }

/-- The stalk maps induced by the absolute Frobenius are local ring homomorphisms. -/
theorem isLocalHom_stalkMap_absoluteFrobenius (p : ℕ) [Fact p.Prime] (X : Scheme.{u})
    [IsCharP X p] (x : X) :
    IsLocalHom ((absoluteFrobeniusToSheafedSpaceHom p X).hom.stalkMap x).hom := sorry

/-- The absolute Frobenius of a scheme `X` in characteristic `p` is the morphism
`X ⟶ X` given by the identity on the underlying topological space and by `g ↦ g ^ p`
on the structure sheaf. -/
@[stacks 03SM]
def absoluteFrobenius (p : ℕ) [Fact p.Prime] (X : Scheme.{u})
    [IsCharP X p] :
    X ⟶ X :=
  Scheme.Hom.mk <|
    LocallyRingedSpace.homMk
      (absoluteFrobeniusToSheafedSpaceHom p X)
      (isLocalHom_stalkMap_absoluteFrobenius p X)

/-- The absolute Frobenius acts by the identity on the underlying topological space. -/
@[stacks 03SM]
theorem absoluteFrobenius_base (p : ℕ) [Fact p.Prime] (X : Scheme.{u})
    [IsCharP X p] :
    (absoluteFrobenius p X).base = 𝟙 (X : TopCat) := sorry

/-- On every open subset, the absolute Frobenius acts on sections by the `p`-th power map. -/
@[stacks 03SM]
theorem absoluteFrobenius_appLE (p : ℕ) [Fact p.Prime] (X : Scheme.{u})
    [IsCharP X p] (U : X.Opens) (s : Γ(X, U)) :
    CommRingCat.Hom.hom ((absoluteFrobenius p X).appLE U U le_rfl) s = s ^ p := sorry

end Scheme

/-- Absolute Frobenius is natural for scheme morphisms in characteristic `p`. -/
@[stacks 0CC7]
theorem absoluteFrobenius_commSq {X Y : Scheme.{u}} {p : ℕ} [Fact p.Prime]
    [Scheme.IsCharP X p] [Scheme.IsCharP Y p] (f : X ⟶ Y) :
    CommSq (Scheme.absoluteFrobenius p X) f f (Scheme.absoluteFrobenius p Y) := sorry

end AlgebraicGeometry
