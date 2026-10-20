/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.RingTheory.Algebra.FreeDimensional

/-!
# The functor of free d-dimensional algebras

The strict presheaf `FA d : Schemeᵒᵖ ⥤ Grpd` sends a scheme `T` to the groupoid of
free `d`-dimensional algebras over `Γ(T, ⊤)`. The fppf decoration on the source
is the ambient site `Scheme.fppfTopology`, not a restriction of objects.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open CategoryTheory Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

private theorem FA_laws (d : ℕ) [NeZero d] :
    (∀ T : Scheme.{u}ᵒᵖ,
      FreeDimAlgebra.baseChangeFunctor (Scheme.Γ.map (𝟙 T)).hom =
        𝟙 (FreeDimAlgebra Γ(T.unop, ⊤) d)) ∧
    (∀ (T T' T'' : Scheme.{u}ᵒᵖ) (f : T ⟶ T') (g : T' ⟶ T''),
      (FreeDimAlgebra.baseChangeFunctor (d := d) (Scheme.Γ.map (f ≫ g)).hom) =
        FreeDimAlgebra.baseChangeFunctor (Scheme.Γ.map f).hom ⋙
          FreeDimAlgebra.baseChangeFunctor (Scheme.Γ.map g).hom) := sorry

/-- The functor sending a scheme `T` to the groupoid of free `d`-dimensional algebras
over `Γ(T, ⊤)`. -/
def FA (d : ℕ) [NeZero d] : Scheme.{u}ᵒᵖ ⥤ Grpd.{u, u} where
  obj T := FreeDimAlgebra Γ(T.unop, ⊤) d
  map f := FreeDimAlgebra.baseChangeFunctor (Scheme.Γ.map f).hom
  map_id := (FA_laws d).1
  map_comp := (FA_laws d).2 _ _ _

/-- The value of `FA d` at a scheme `T` is the groupoid of free `d`-dimensional
algebras over `Γ(T, ⊤)`. -/
theorem FA_obj (d : ℕ) [NeZero d] (T : Scheme.{u}) :
    (FA d).obj (op T) = FreeDimAlgebra Γ(T, ⊤) d := sorry

/-- Restriction of objects of `FA d` along a morphism of schemes is base change
along the induced map on global sections. -/
theorem FA_map_obj (d : ℕ) [NeZero d] {T T' : Scheme.{u}ᵒᵖ} (f : T ⟶ T')
    (m : FreeDimAlgebra Γ(T.unop, ⊤) d) :
    ((FA d).map f).obj m = FreeDimAlgebra.baseChange (Scheme.Γ.map f).hom m := sorry

/-- The functor `FA d` pulled back along `Over.forget` to schemes over `S`. -/
def FA.over (d : ℕ) [NeZero d] (S : Scheme.{u}) : (Over S)ᵒᵖ ⥤ Grpd.{u, u} :=
  (Over.forget S).op ⋙ FA d

end AlgebraicGeometry
