/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ProjectionEquivalence.Left
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ProjectionEquivalence.Right

/-!
# Directional comparison computations for pseudopullback projection equivalences

The standard left- and right-equivalence cones already expose their whole comparison
isomorphisms. This leaf adds the oriented `hom` and `inv` cells as atomic rewrite rules, so
downstream compatibility calculations do not need to unfold a composite `Iso`.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

/-- The forward comparison cell of the standard left-equivalence cone is the displayed
associator/counit/unitor composite. -/
@[simp]
theorem ofLeftEquivalence.iso.hom
    (hf : Bicategory.Equivalence.OnHom f) (g : y ⟶ z) :
    (ofLeftEquivalence hf g).iso.hom =
      (α_ g hf.inv f).hom ≫
        (Bicategory.whiskerLeftIso g hf.counit).hom ≫
          (ρ_ g).hom ≫ (λ_ g).inv := sorry

/-- The inverse comparison cell of the standard left-equivalence cone reverses the displayed
associator/counit/unitor composite. -/
@[simp]
theorem ofLeftEquivalence.iso.inv
    (hf : Bicategory.Equivalence.OnHom f) (g : y ⟶ z) :
    (ofLeftEquivalence hf g).iso.inv =
      (λ_ g).hom ≫
        (ρ_ g).inv ≫
          (Bicategory.whiskerLeftIso g hf.counit).inv ≫ (α_ g hf.inv f).inv := sorry

/-- The forward comparison cell of the standard right-equivalence cone is the displayed
unitor/counit/associator composite. -/
@[simp]
theorem ofRightEquivalence.iso.hom
    (f : x ⟶ z) (hg : Bicategory.Equivalence.OnHom g) :
    (ofRightEquivalence f hg).iso.hom =
      (λ_ f).hom ≫
        (ρ_ f).inv ≫
          (Bicategory.whiskerLeftIso f hg.counit).inv ≫ (α_ f hg.inv g).inv := sorry

/-- The inverse comparison cell of the standard right-equivalence cone reverses the displayed
unitor/counit/associator composite. -/
@[simp]
theorem ofRightEquivalence.iso.inv
    (f : x ⟶ z) (hg : Bicategory.Equivalence.OnHom g) :
    (ofRightEquivalence f hg).iso.inv =
      (α_ f hg.inv g).hom ≫
        (Bicategory.whiskerLeftIso f hg.counit).hom ≫
          (ρ_ f).hom ≫ (λ_ f).inv := sorry

end Bicategory.PseudoPullbackCone

end CategoryTheory
