/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Equivalence

/-!
# Compatibility of algebraic-space presentations with recovered morphisms
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.toGroupoids

/-- A morphism of presented groupoid fibrations agrees, through the presentation
 equivalences, with the morphism recovered by fiberwise evaluation. -/
def presentationIso {S : Scheme.{u}} {F G : AlgebraicSpace S}
    {X Y : GroupoidsOver S} (eX : X ≌ F.toGroupoids) (eY : Y ≌ G.toGroupoids)
    (f : X ⟶ Y) :
    f ≫ eY.hom ≅ eX.hom ≫ map (recover eX eY f) := by
  let P := (eX.inv ≫ f) ≫ eY.hom
  let h := eval P
  let components (a : F.toGroupoids.total) :
      (toFunctor P).obj a ≅ (toFunctor (map h)).obj a :=
    (eqToIso (congrArg Subtype.val
      (Sets.ofPresheaf.valueToFiber.leftInverse G.functorOfPoints
        (F.toGroupoids.p.obj a)
        ((fiberFunctor P (F.toGroupoids.p.obj a)).obj
          (Sets.ofPresheaf.valueToFiber F.functorOfPoints
            (F.toGroupoids.p.obj a) a.unop.2))))).symm
  have coherence :
      (∀ {a b : F.toGroupoids.total} (k : a ⟶ b),
        (toFunctor P).map k ≫ (components b).hom =
          (components a).hom ≫ (toFunctor (map h)).map k) ∧
      (∀ a : F.toGroupoids.total,
        G.toGroupoids.p.IsHomLift (𝟙 (F.toGroupoids.p.obj a))
          (components a).hom) := sorry
  let β : P ≅ map h :=
    BasedFunctorIso.lift
      (BasedNatIso.ofComponents components coherence.1 coherence.2)
  exact (Bicategory.leftUnitor (f ≫ eY.hom)).symm ≪≫
    Bicategory.whiskerRightIso eX.unit (f ≫ eY.hom) ≪≫
    Bicategory.associator eX.hom eX.inv (f ≫ eY.hom) ≪≫
    Bicategory.whiskerLeftIso eX.hom
      (Bicategory.associator eX.inv f eY.hom).symm ≪≫
    Bicategory.whiskerLeftIso eX.hom β

end AlgebraicGeometry.AlgebraicSpace.toGroupoids
