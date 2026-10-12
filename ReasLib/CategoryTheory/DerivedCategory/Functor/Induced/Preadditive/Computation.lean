/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Preadditive
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Computation for composite homotopy-to-derived functors

This leaf exposes the components and naturality of the canonical comparison
between the homotopy-to-derived functor attached to an additive functor and
the two-stage construction attached to an isomorphic composite.
-/

@[expose] public section

open CategoryTheory
open ComplexShape

noncomputable section

universe uA vA uB vB uC vC

namespace CategoryTheory.Functor.Homotopy.Comp.isoOfIso

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory C]

/-- The forward component of the comparison is the image under localization
of the inverse homotopy-category composition comparison. -/
@[stacks 05S3 "composite homotopy-to-derived computation"]
theorem hom_app (F : A ⥤ B) (G : B ⥤ C) {H : A ⥤ C}
    [F.Additive] [G.Additive] [H.Additive] (hcomp : H ≅ F ⋙ G)
    (K : HomotopyCategory A (up ℤ)) :
    (isoOfIso F G hcomp).hom.app K =
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso hcomp.symm (up ℤ)).inv.app K) := sorry

/-- The inverse component of the comparison is the image under localization
of the forward homotopy-category composition comparison. -/
@[stacks 05S3 "composite homotopy-to-derived computation"]
theorem inv_app (F : A ⥤ B) (G : B ⥤ C) {H : A ⥤ C}
    [F.Additive] [G.Additive] [H.Additive] (hcomp : H ≅ F ⋙ G)
    (K : HomotopyCategory A (up ℤ)) :
    (isoOfIso F G hcomp).inv.app K =
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso hcomp.symm (up ℤ)).hom.app K) := sorry

/-- Forward naturality of the comparison between a functor and an isomorphic
composite, written using the two induced functors seen by downstream users. -/
@[reassoc (attr := simp), stacks 05S3 "composite homotopy-to-derived computation"]
theorem hom_naturality (F : A ⥤ B) (G : B ⥤ C) {H : A ⥤ C}
    [F.Additive] [G.Additive] [H.Additive] (hcomp : H ≅ F ⋙ G)
    {K L : HomotopyCategory A (up ℤ)} (f : K ⟶ L) :
    (Homotopy.toDerived H).map f ≫ (isoOfIso F G hcomp).hom.app L =
      (isoOfIso F G hcomp).hom.app K ≫ (toDerived F G).map f := sorry

/-- Inverse naturality of the comparison between a functor and an isomorphic
composite, written using the two induced functors seen by downstream users. -/
@[reassoc (attr := simp), stacks 05S3 "composite homotopy-to-derived computation"]
theorem inv_naturality (F : A ⥤ B) (G : B ⥤ C) {H : A ⥤ C}
    [F.Additive] [G.Additive] [H.Additive] (hcomp : H ≅ F ⋙ G)
    {K L : HomotopyCategory A (up ℤ)} (f : K ⟶ L) :
    (toDerived F G).map f ≫ (isoOfIso F G hcomp).inv.app L =
      (isoOfIso F G hcomp).inv.app K ≫ (Homotopy.toDerived H).map f := sorry


end CategoryTheory.Functor.Homotopy.Comp.isoOfIso
