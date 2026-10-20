/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Forgetful
public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.RelativeMap
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation

/-!
# LCI locus in a finite Hilbert stack

The full subcategory `H_{d,lci}(X/Y) ⊂ H_d(X/Y)` consists of those objects
whose recovered morphism `relativeSpaceHom` into a representing algebraic space
`X_y` is unramified and a local complete intersection.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Functor
open FiberedCategoryOver.Groupoids
open StackOver.Groupoids.Hom
open scoped Bicategory CategoryTheory.TwoFibreProduct

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {X Y : GroupoidsOver S}

/-- An object `ξ` of `H_d(X/Y)` lies in the LCI locus when, for every algebraic-space
presentation of `relativeApex F ξ` over `ξ.U`, the recovered morphism
`relativeSpaceHom F ξ Xy e` is unramified and a local complete intersection. -/
def Obj.IsLci (F : X ⟶ Y) {d : ℕ} (ξ : Obj F d) : Prop :=
  ∀ (Xy : AlgebraicSpace S) (fy : Xy ⟶ ofOver ξ.U)
    (e : relativeApex F ξ ≌ Xy.toGroupoids),
    Nonempty
        (e.hom ≫ toGroupoids.map fy ≫ (ofOverSliceEquiv ξ.U).hom ≅
          TwoFibreProduct.fst.{u + 1, u, u + 1, u}
            (YonedaSlice.representative ξ.y) F) →
      AlgebraicSpace.Unramified (relativeSpaceHom F ξ Xy e) ∧
        AlgebraicSpace.IsLocalCompleteIntersection (relativeSpaceHom F ξ Xy e)

/-- Membership in the LCI locus is equivalent to unramifiedness and the local complete
intersection property of `relativeSpaceHom` on every compatible presentation. -/
theorem Obj.isLci_iff (F : X ⟶ Y) {d : ℕ} (ξ : Obj F d) :
    Obj.IsLci F ξ ↔
      ∀ (Xy : AlgebraicSpace S) (fy : Xy ⟶ ofOver ξ.U)
        (e : relativeApex F ξ ≌ Xy.toGroupoids),
        Nonempty
            (e.hom ≫ toGroupoids.map fy ≫ (ofOverSliceEquiv ξ.U).hom ≅
              TwoFibreProduct.fst.{u + 1, u, u + 1, u}
                (YonedaSlice.representative ξ.y) F) →
          AlgebraicSpace.Unramified (relativeSpaceHom F ξ Xy e) ∧
            AlgebraicSpace.IsLocalCompleteIntersection (relativeSpaceHom F ξ Xy e) :=
  sorry

/-- On a compatible presentation, an LCI-locus object has unramified `relativeSpaceHom`. -/
theorem Obj.isLci_unramified (F : X ⟶ Y) {d : ℕ} {ξ : Obj F d}
    (hξ : Obj.IsLci F ξ) (Xy : AlgebraicSpace S) (fy : Xy ⟶ ofOver ξ.U)
    (e : relativeApex F ξ ≌ Xy.toGroupoids)
    (h_fst : Nonempty
      (e.hom ≫ toGroupoids.map fy ≫ (ofOverSliceEquiv ξ.U).hom ≅
        TwoFibreProduct.fst.{u + 1, u, u + 1, u}
          (YonedaSlice.representative ξ.y) F)) :
    AlgebraicSpace.Unramified (relativeSpaceHom F ξ Xy e) :=
  sorry

/-- On a compatible presentation, an LCI-locus object has local complete intersection
`relativeSpaceHom`. -/
theorem Obj.isLci_lci (F : X ⟶ Y) {d : ℕ} {ξ : Obj F d}
    (hξ : Obj.IsLci F ξ) (Xy : AlgebraicSpace S) (fy : Xy ⟶ ofOver ξ.U)
    (e : relativeApex F ξ ≌ Xy.toGroupoids)
    (h_fst : Nonempty
      (e.hom ≫ toGroupoids.map fy ≫ (ofOverSliceEquiv ξ.U).hom ≅
        TwoFibreProduct.fst.{u + 1, u, u + 1, u}
          (YonedaSlice.representative ξ.y) F)) :
    AlgebraicSpace.IsLocalCompleteIntersection (relativeSpaceHom F ξ Xy e) :=
  sorry

/-- The object property on `H_d(X/Y)` cut out by the LCI locus. -/
def lci (F : X ⟶ Y) (d : ℕ) : ObjectProperty (Obj F d) :=
  fun ξ ↦ Obj.IsLci F ξ

/-- The object property `lci F d` is the LCI-locus predicate on objects of `H_d(X/Y)`. -/
theorem lci_iff (F : X ⟶ Y) (d : ℕ) (ξ : Obj F d) :
    lci F d ξ ↔ Obj.IsLci F ξ :=
  sorry

/-- The LCI locus is closed under isomorphisms in `H_d(X/Y)`. -/
instance lci.isClosedUnderIsomorphisms (F : X ⟶ Y) (d : ℕ) :
    (lci F d).IsClosedUnderIsomorphisms :=
  sorry

variable {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- Restricted Hilbert projection of the LCI locus in `H_d(𝒳/𝒴)`. -/
def lciP (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    (lci (asGroupoidsOverMor F) d).FullSubcategory ⥤ Over S :=
  (lci (asGroupoidsOverMor F) d).ι ⋙ p (asGroupoidsOverMor F) d

/-- The restricted projection sends an LCI object to its test scheme. -/
theorem lciP_obj (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    (ξ : (lci (asGroupoidsOverMor F) d).FullSubcategory) :
    (lciP F d).obj ξ = ξ.obj.U :=
  sorry

/-- The restricted LCI projection is a stack in groupoids over `(Sch/S)_fppf`. -/
theorem lciP_isStack (F : 𝒳 ⟶ 𝒴)
    [Groupoids.Hom.Flat (asGroupoidsOverMor F)]
    [Groupoids.Hom.LocallyOfFinitePresentation (asGroupoidsOverMor F)] (d : ℕ) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (lciP F d) :=
  sorry

/-- The stack in groupoids `H_{d,lci}(𝒳/𝒴)` of LCI Hilbert objects of degree `d`. -/
def lciStack (F : 𝒳 ⟶ 𝒴)
    [Groupoids.Hom.Flat (asGroupoidsOverMor F)]
    [Groupoids.Hom.LocallyOfFinitePresentation (asGroupoidsOverMor F)] (d : ℕ) :
    StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S) :=
  StackOver.Groupoids.ofProjectionWith (Scheme.fppfTopology.over S) (lciP F d)
    (lciP_isStack F d)

/-- The projection of `lciStack F d` is the restricted Hilbert forgetful functor. -/
theorem lciStack_p (F : 𝒳 ⟶ 𝒴)
    [Groupoids.Hom.Flat (asGroupoidsOverMor F)]
    [Groupoids.Hom.LocallyOfFinitePresentation (asGroupoidsOverMor F)] (d : ℕ) :
    (lciStack F d).p = lciP F d :=
  sorry

/-- The inclusion of total categories `H_{d,lci}(𝒳/𝒴) ⟶ H_d(𝒳/𝒴)` lies over
`(Sch/S)_fppf`. -/
theorem lciInclusion_w (F : 𝒳 ⟶ 𝒴)
    [Groupoids.Hom.Flat (asGroupoidsOverMor F)]
    [Groupoids.Hom.LocallyOfFinitePresentation (asGroupoidsOverMor F)] (d : ℕ) :
    (lci (asGroupoidsOverMor F) d).ι ⋙ (stack (asGroupoidsOverMor F) d).p =
      (lciStack F d).p :=
  sorry

/-- The based inclusion of `H_{d,lci}(𝒳/𝒴)` into `H_d(𝒳/𝒴)`. -/
def lciInclusionBased (F : 𝒳 ⟶ 𝒴)
    [Groupoids.Hom.Flat (asGroupoidsOverMor F)]
    [Groupoids.Hom.LocallyOfFinitePresentation (asGroupoidsOverMor F)] (d : ℕ) :
    (lciStack F d).toBasedCategory ⥤ᵇ
      (stack (asGroupoidsOverMor F) d).toBasedCategory where
  toFunctor := (lci (asGroupoidsOverMor F) d).ι
  w := lciInclusion_w F d

/-- The inclusion 1-morphism `H_{d,lci}(𝒳/𝒴) ⟶ H_d(𝒳/𝒴)` of stacks in groupoids. -/
def lciInclusion (F : 𝒳 ⟶ 𝒴)
    [Groupoids.Hom.Flat (asGroupoidsOverMor F)]
    [Groupoids.Hom.LocallyOfFinitePresentation (asGroupoidsOverMor F)] (d : ℕ) :
    lciStack F d ⟶ stack (asGroupoidsOverMor F) d :=
  lift (ofBasedFunctor (lciInclusionBased F d))

/-- The object map of `lciInclusion` is the full-subcategory inclusion. -/
theorem lciInclusion_obj (F : 𝒳 ⟶ 𝒴)
    [Groupoids.Hom.Flat (asGroupoidsOverMor F)]
    [Groupoids.Hom.LocallyOfFinitePresentation (asGroupoidsOverMor F)] (d : ℕ)
    (ξ : (lci (asGroupoidsOverMor F) d).FullSubcategory) :
    (lciInclusionBased F d).obj ξ = ξ.obj :=
  sorry

/-- The forgetful 1-morphism `H_{d,lci}(𝒳/𝒴) ⟶ 𝒴`. -/
def lciForgetToY (F : 𝒳 ⟶ 𝒴)
    [Groupoids.Hom.Flat (asGroupoidsOverMor F)]
    [Groupoids.Hom.LocallyOfFinitePresentation (asGroupoidsOverMor F)] (d : ℕ) : lciStack F d ⟶ 𝒴 :=
  lciInclusion F d ≫ forgetToY F d

/-- The LCI forgetful map factors as the inclusion followed by `forgetToY`. -/
theorem lciInclusion_comp_forgetToY (F : 𝒳 ⟶ 𝒴)
    [Groupoids.Hom.Flat (asGroupoidsOverMor F)]
    [Groupoids.Hom.LocallyOfFinitePresentation (asGroupoidsOverMor F)] (d : ℕ) :
    lciInclusion F d ≫ forgetToY F d = lciForgetToY F d :=
  sorry

end AlgebraicGeometry.FiniteHilbertStack
