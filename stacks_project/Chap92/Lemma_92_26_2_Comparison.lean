/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentComplex.EtaleLocalization

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Cotangent

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.baseChangeSimplicialHom :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {A A' O : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}}
    (α : A ⟶ A') (φ : A ⟶ O) (φ' : A' ⟶ O)
    (hα : α ≫ φ' = φ ≫ 𝟙 O) (n : SimplexCategoryᵒᵖ),
    (simplicialModule A (Under.mk φ)).obj n ⟶
      (simplicialModule A' (Under.mk φ')).obj n)

#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.etaleRestrictIso :
  ∀ {S : Scheme.{u}} {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (q : V ⟶ Y) (g : U ⟶ V) (f : X ⟶ Y)
    [Etale p] [Etale q] (sq : CommSq g p q f),
    Cotangent.pullbackCotangent p f ≅ Cotangent.cotangent g)
