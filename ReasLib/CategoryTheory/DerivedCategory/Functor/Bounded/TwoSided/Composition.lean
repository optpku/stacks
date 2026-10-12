/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.TwoSided.Basic
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Map.Computation

/-!
# Composition of two-sided bounded induced functors

The bounded functor induced by a composite agrees with the two-stage functor obtained by mapping
the homotopy category first and then applying the second bounded induced functor.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.toBoundedDerived

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
  [Preadditive A] [Preadditive B] [Abelian C]
  [HasDerivedCategory.{w} C]

/-- The two-stage functor `Kᵇ(A) ⥤ Dᵇ(C)` obtained by first applying `F : A ⥤ B`,
then applying `G : B ⥤ C`, and finally passing to `Dᵇ(C)`. -/
@[stacks 05T4 "two-stage bounded derived functor"]
def comp (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    HomotopyCategory.Bounded A ⥤ DerivedCategory.Bounded C :=
  F.mapHomotopyCategoryBounded ⋙ G.toBoundedDerived

/-- If `H : A ⥤ C` is isomorphic to `F ⋙ G`, the bounded functor induced by `H` is
canonically isomorphic to the two-stage functor induced by `F` and `G`. -/
@[stacks 05T4 "bounded composition comparison from an underived isomorphism"]
noncomputable def compIsoOfIso
    (F : A ⥤ B) (G : B ⥤ C) {H : A ⥤ C}
    [F.Additive] [G.Additive] [H.Additive] (hcomp : H ≅ F ⋙ G) :
    H.toBoundedDerived ≅ comp F G :=
  Functor.isoWhiskerRight
      (Functor.Homotopy.Bounded.compIso hcomp.symm).symm
      (DerivedCategory.Bounded.Qh C) ≪≫
    Functor.associator F.mapHomotopyCategoryBounded
      G.mapHomotopyCategoryBounded (DerivedCategory.Bounded.Qh C)

/-- The forward component of the bounded composition comparison is localization of the inverse
homotopy-category comparison. -/
@[simp]
theorem compIsoOfIso_hom_app
    (F : A ⥤ B) (G : B ⥤ C) {H : A ⥤ C}
    [F.Additive] [G.Additive] [H.Additive] (hcomp : H ≅ F ⋙ G)
    (X : HomotopyCategory.Bounded A) :
    (compIsoOfIso F G hcomp).hom.app X =
      (DerivedCategory.Bounded.Qh C).map
        ((Functor.Homotopy.Bounded.compIso hcomp.symm).inv.app X) := sorry

/-- The inverse component of the bounded composition comparison is localization of the forward
homotopy-category comparison. -/
@[simp]
theorem compIsoOfIso_inv_app
    (F : A ⥤ B) (G : B ⥤ C) {H : A ⥤ C}
    [F.Additive] [G.Additive] [H.Additive] (hcomp : H ≅ F ⋙ G)
    (X : HomotopyCategory.Bounded A) :
    (compIsoOfIso F G hcomp).inv.app X =
      (DerivedCategory.Bounded.Qh C).map
        ((Functor.Homotopy.Bounded.compIso hcomp.symm).hom.app X) := sorry

/-- The bounded functor induced by `F ⋙ G` is canonically isomorphic to the two-stage functor
induced by `F` and `G`. -/
@[stacks 05T4 "bounded composition comparison"]
noncomputable def compIso
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    (F ⋙ G).toBoundedDerived ≅ comp F G :=
  compIsoOfIso F G (Iso.refl (F ⋙ G))

end CategoryTheory.Functor.toBoundedDerived
