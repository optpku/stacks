/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.RelativeHom.Presheaf

universe u

open CategoryTheory

/-
37.68.0.2: For schemes `Z` and `X` over `S`, the relative-Hom presheaf sends an
`S`-scheme `T` to the type of base-change morphisms `b` over `T` from
`T ×_S Z` to `T ×_S X`, equivalently the type of `S`-morphisms `T ⊗ Z ⟶ X`.
-/
@[stacks 0BL2] #check
  (AlgebraicGeometry.Scheme.RelativeHom.functor :
    ∀ {S : AlgebraicGeometry.Scheme.{u}},
      CategoryTheory.Over S → CategoryTheory.Over S →
        (CategoryTheory.Over S)ᵒᵖ ⥤ Type u)

#check
  (AlgebraicGeometry.Scheme.RelativeHom.baseChangeMorphismEquiv :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (Z X T : CategoryTheory.Over S),
      AlgebraicGeometry.Scheme.RelativeHom.BaseChangeMorphism Z X T ≃
        (AlgebraicGeometry.Scheme.RelativeHom.functor Z X).obj (.op T))

#check AlgebraicGeometry.Scheme.RelativeHom.functor_obj
#check AlgebraicGeometry.Scheme.RelativeHom.functor_map
