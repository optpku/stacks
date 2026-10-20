/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Homotopy-to-Derived Functors from Preadditive Sources

This leaf gives the generic functor from the homotopy category of a
preadditive source to the derived category of an abelian target.  The source
need not itself be abelian or have a derived category.
-/

@[expose] public section

open CategoryTheory
open ComplexShape

noncomputable section

universe uA vA uB vB uC vC

namespace CategoryTheory.Functor

namespace Homotopy

section Basic

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory B]

/-- The homotopy-to-derived functor induced by an additive functor from a preadditive source.
In particular, the source need not be abelian or carry its own derived category. -/
@[stacks 05S3 "homotopy-to-derived functor from a preadditive source"]
def toDerived (F : A ⥤ B) [F.Additive] :
    HomotopyCategory A (up ℤ) ⥤ DerivedCategory B :=
  F.mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The homotopy-to-derived functor induced by an additive functor commutes
with the integer shift. -/
@[stacks 05S3 "homotopy-to-derived functor from a preadditive source"]
noncomputable instance toDerived.commShift (F : A ⥤ B) [F.Additive] :
    (toDerived F).CommShift ℤ :=
  inferInstanceAs
    ((F.mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh).CommShift ℤ)

/-- The homotopy-to-derived functor induced by an additive functor is
triangulated. -/
@[stacks 05S3 "homotopy-to-derived functor from a preadditive source"]
instance toDerived.isTriangulated [Limits.HasZeroObject A] [Limits.HasBinaryBiproducts A]
    (F : A ⥤ B) [F.Additive] :
    (toDerived F).IsTriangulated :=
  inferInstanceAs
    ((F.mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh).IsTriangulated)

/-- The objectwise computation for `toDerived`. -/
@[stacks 05S3 "homotopy-to-derived functor from a preadditive source", simp]
theorem toDerived_obj (F : A ⥤ B) [F.Additive]
    (K : HomotopyCategory A (up ℤ)) :
    (Homotopy.toDerived F).obj K =
      DerivedCategory.Qh.obj ((F.mapHomotopyCategory (up ℤ)).obj K) := sorry

/-- The morphismwise computation for `toDerived`. -/
@[stacks 05S3 "homotopy-to-derived functor from a preadditive source", simp]
theorem toDerived_map (F : A ⥤ B) [F.Additive]
    {K L : HomotopyCategory A (up ℤ)} (f : K ⟶ L) :
    (Homotopy.toDerived F).map f =
      DerivedCategory.Qh.map ((F.mapHomotopyCategory (up ℤ)).map f) := sorry

end Basic

section HomotopyComposition

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B]
variable {C : Type uC} [Category.{vC} C] [Preadditive C]

/-- The composite action of two additive functors on homotopy categories. -/
@[stacks 05S3 "composition on homotopy categories"]
def comp (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    HomotopyCategory A (up ℤ) ⥤ HomotopyCategory C (up ℤ) :=
  F.mapHomotopyCategory (up ℤ) ⋙ G.mapHomotopyCategory (up ℤ)

/-- The objectwise computation for `comp`. -/
@[stacks 05S3 "composition on homotopy categories", simp]
theorem comp_obj (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] (K : HomotopyCategory A (up ℤ)) :
    (comp F G).obj K =
      (G.mapHomotopyCategory (up ℤ)).obj ((F.mapHomotopyCategory (up ℤ)).obj K) := sorry

/-- The morphismwise computation for `comp`. -/
@[stacks 05S3 "composition on homotopy categories", simp]
theorem comp_map (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] {K L : HomotopyCategory A (up ℤ)} (f : K ⟶ L) :
    (comp F G).map f =
      (G.mapHomotopyCategory (up ℤ)).map ((F.mapHomotopyCategory (up ℤ)).map f) := sorry

end HomotopyComposition

section DerivedComposition

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory C]

namespace Comp

/-- The homotopy-to-derived functor obtained from a composable pair of additive functors. -/
@[stacks 05S3 "composite homotopy-to-derived functor",
  stacks 0FTE "pullback followed by tensoring on homotopy categories"]
def toDerived (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] :
    HomotopyCategory A (up ℤ) ⥤ DerivedCategory C :=
  Homotopy.comp F G ⋙ DerivedCategory.Qh

/-- The objectwise computation for `Comp.toDerived`. -/
@[stacks 05S3 "composite homotopy-to-derived functor", simp]
theorem toDerived_obj (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] (K : HomotopyCategory A (up ℤ)) :
    (toDerived F G).obj K =
      DerivedCategory.Qh.obj ((Homotopy.comp F G).obj K) := sorry

/-- The morphismwise computation for `Comp.toDerived`. -/
@[stacks 05S3 "composite homotopy-to-derived functor", simp]
theorem toDerived_map (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] {K L : HomotopyCategory A (up ℤ)} (f : K ⟶ L) :
    (toDerived F G).map f =
      DerivedCategory.Qh.map ((Homotopy.comp F G).map f) := sorry

/-- The canonical comparison from the homotopy-to-derived functor of a functor isomorphic to a
composite to the corresponding two-stage homotopy-to-derived construction. -/
@[stacks 05S3 "composite homotopy-to-derived functor"]
noncomputable def isoOfIso
    (F : A ⥤ B) (G : B ⥤ C) {H : A ⥤ C}
    [F.Additive] [G.Additive] [H.Additive] (hcomp : H ≅ F ⋙ G) :
    Homotopy.toDerived H ≅ toDerived F G :=
  Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso hcomp.symm (up ℤ)).symm
    (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C)

/-- The canonical comparison from the homotopy-to-derived functor of a composite to the
two-stage homotopy-to-derived construction. -/
@[stacks 05S3 "composite homotopy-to-derived functor"]
noncomputable def iso (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] :
    Homotopy.toDerived (F ⋙ G) ≅ toDerived F G :=
  isoOfIso F G (Iso.refl (F ⋙ G))

/-- The two-stage homotopy-to-derived construction is isomorphic to that of every additive
functor equipped with a comparison to the underived composite. -/
@[stacks 05S3 "composite homotopy-to-derived functor"]
theorem isomorphicOfIso
    (F : A ⥤ B) (G : B ⥤ C) {H : A ⥤ C}
    [F.Additive] [G.Additive] [H.Additive] (hcomp : H ≅ F ⋙ G) :
    IsIsomorphic (toDerived F G) (Homotopy.toDerived H) := sorry

/-- The comparison from a two-stage homotopy-to-derived construction to the functor induced by
the composite is invertible. -/
@[stacks 05S3 "composite homotopy-to-derived functor"]
theorem isomorphic (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] :
    IsIsomorphic (toDerived F G) (Homotopy.toDerived (F ⋙ G)) := sorry



end Comp

end DerivedComposition


end Homotopy

end CategoryTheory.Functor
