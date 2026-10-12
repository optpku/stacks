/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
public import stacks_project.Chap97.«97_13_0_2_FreeDimAlgebra»

/-!
# The functor of free d-dimensional algebras

The strict presheaf `FA d : Schemeᵒᵖ ⥤ Grpd` sends a scheme `T` to the groupoid of
free `d`-dimensional algebras over `Γ(T, ⊤)`. The fppf decoration on the source
is the ambient site `Scheme.fppfTopology`, not a restriction of objects.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The functor sending a scheme `T` to the groupoid of free `d`-dimensional algebras
over `Γ(T, ⊤)`. -/
def FA (d : ℕ) [NeZero d] : Scheme.{u}ᵒᵖ ⥤ Grpd.{u, u} where
  obj T := Grpd.of (FreeDimAlgebra Γ(T.unop, ⊤) d)
  map f := FreeDimAlgebra.baseChangeFunctor (Scheme.Γ.map f).hom
  map_id := sorry
  map_comp := sorry

/-- The value of `FA d` at a scheme `T` is the groupoid of free `d`-dimensional
algebras over `Γ(T, ⊤)`. -/
theorem FA_obj (d : ℕ) [NeZero d] (T : Scheme.{u}) :
    (FA d).obj (op T) = Grpd.of (FreeDimAlgebra Γ(T, ⊤) d) := sorry

/-- Restriction of objects of `FA d` along a morphism of schemes is base change
along the induced map on global sections. -/
theorem FA_map_obj (d : ℕ) [NeZero d] {T T' : Scheme.{u}ᵒᵖ} (f : T ⟶ T')
    (m : FreeDimAlgebra Γ(T.unop, ⊤) d) :
    ((FA d).map f).obj m = FreeDimAlgebra.baseChange (Scheme.Γ.map f).hom m := sorry

/-- The functor `FA d` pulled back along `Over.forget` to schemes over `S`. -/
def FA.over (d : ℕ) [NeZero d] (S : Scheme.{u}) : (Over S)ᵒᵖ ⥤ Grpd.{u, u} :=
  (Over.forget S).op ⋙ FA d

end AlgebraicGeometry
