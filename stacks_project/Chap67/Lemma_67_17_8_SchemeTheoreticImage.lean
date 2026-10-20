/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage

/-!
# Compatibility checks for scheme-theoretic dominance of algebraic spaces
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {B X Y U W : AlgebraicSpace S}

#check (IsSchemeTheoreticallyDominant :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

#check (IsSchemeTheoreticallyDominant.spec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    IsSchemeTheoreticallyDominant f ↔
      ∀ {Z : AlgebraicSpace S} (i : Z ⟶ Y) [IsClosedImmersion i] (h : X ⟶ Z),
        h ≫ i = f → IsIso i)

#check (IsSchemeTheoreticallyDominant.id :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S},
    IsSchemeTheoreticallyDominant (𝟙 X))

#check (IsSchemeTheoreticallyDominant.of_isIso :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIso f],
    IsSchemeTheoreticallyDominant f)

#check (ext_of_isSchemeTheoreticallyDominant_of_isSeparated :
  ∀ {S : Scheme.{u}} {B X Y W : AlgebraicSpace S}
    [OverClass X B] [OverClass Y B] [Separated (Y ↘ B)]
    {f g : X ⟶ Y} [HomIsOver f B] [HomIsOver g B]
    (ι : W ⟶ X) [IsSchemeTheoreticallyDominant ι],
    ι ≫ f = ι ≫ g → f = g)

#check (ext_of_schemeTheoreticClosure_of_isSeparated :
  ∀ {S : Scheme.{u}} {B X Y U : AlgebraicSpace S}
    [OverClass X B] [OverClass Y B] [Separated (Y ↘ B)]
    {f g : X ⟶ Y} [HomIsOver f B] [HomIsOver g B]
    (ι : U ⟶ X) [IsOpenImmersion ι] [IsSchemeTheoreticallyDominant ι],
    ι ≫ f = ι ≫ g → f = g)

end AlgebraicGeometry.AlgebraicSpace
