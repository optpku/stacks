/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Map.Projection.Construction

/-!
# Computations for endpoint projections after mapping bundled cospans

The three projection comparisons have identity components.  Their forward and inverse naturality
cells are the corresponding unitor composites on the mapped vertex morphism.
-/

@[expose] public section

universe w v u w' v' u'

namespace CategoryTheory.Bicategory.Cospan

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

variable {B : Type u} [Bicategory.{w, v} B]
variable {B' : Type u'} [Bicategory.{w', v'} B']

/-- The left-projection comparison has the identity component. -/
@[simp]
theorem map.leftProjection.app (P : B ⥤ᵖ B') (S : Cospan B) :
    (map.leftProjection P).app S = 𝟙 (P.obj S.left) := sorry

/-- The right-projection comparison has the identity component. -/
@[simp]
theorem map.rightProjection.app (P : B ⥤ᵖ B') (S : Cospan B) :
    (map.rightProjection P).app S = 𝟙 (P.obj S.right) := sorry

/-- The base-projection comparison has the identity component. -/
@[simp]
theorem map.baseProjection.app (P : B ⥤ᵖ B') (S : Cospan B) :
    (map.baseProjection P).app S = 𝟙 (P.obj S.base) := sorry

/-- Naturality of the left-projection comparison is its canonical unitor isomorphism. -/
@[simp]
theorem map.leftProjection.naturality (P : B ⥤ᵖ B')
    {S T : Cospan B} (psi : S ⟶ T) :
    (map.leftProjection P).naturality psi =
      map.leftProjection.naturalityIso P psi := sorry

/-- Naturality of the right-projection comparison is its canonical unitor isomorphism. -/
@[simp]
theorem map.rightProjection.naturality (P : B ⥤ᵖ B')
    {S T : Cospan B} (psi : S ⟶ T) :
    (map.rightProjection P).naturality psi =
      map.rightProjection.naturalityIso P psi := sorry

/-- Naturality of the base-projection comparison is its canonical unitor isomorphism. -/
@[simp]
theorem map.baseProjection.naturality (P : B ⥤ᵖ B')
    {S T : Cospan B} (psi : S ⟶ T) :
    (map.baseProjection P).naturality psi =
      map.baseProjection.naturalityIso P psi := sorry

/-- The forward left-projection naturality cell is the unitor composite on the mapped left
component. -/
@[simp]
theorem map.leftProjection.naturality.hom (P : B ⥤ᵖ B')
    {S T : Cospan B} (psi : S ⟶ T) :
    ((map.leftProjection P).naturality psi).hom =
      (ρ_ (P.map (Hom.left psi))).hom ≫
        (λ_ (P.map (Hom.left psi))).inv := sorry

/-- The inverse left-projection naturality cell is the reverse unitor composite on the mapped
left component. -/
@[simp]
theorem map.leftProjection.naturality.inv (P : B ⥤ᵖ B')
    {S T : Cospan B} (psi : S ⟶ T) :
    ((map.leftProjection P).naturality psi).inv =
      (λ_ (P.map (Hom.left psi))).hom ≫
        (ρ_ (P.map (Hom.left psi))).inv := sorry

/-- The forward right-projection naturality cell is the unitor composite on the mapped right
component. -/
@[simp]
theorem map.rightProjection.naturality.hom (P : B ⥤ᵖ B')
    {S T : Cospan B} (psi : S ⟶ T) :
    ((map.rightProjection P).naturality psi).hom =
      (ρ_ (P.map (Hom.right psi))).hom ≫
        (λ_ (P.map (Hom.right psi))).inv := sorry

/-- The inverse right-projection naturality cell is the reverse unitor composite on the mapped
right component. -/
@[simp]
theorem map.rightProjection.naturality.inv (P : B ⥤ᵖ B')
    {S T : Cospan B} (psi : S ⟶ T) :
    ((map.rightProjection P).naturality psi).inv =
      (λ_ (P.map (Hom.right psi))).hom ≫
        (ρ_ (P.map (Hom.right psi))).inv := sorry

/-- The forward base-projection naturality cell is the unitor composite on the mapped base
component. -/
@[simp]
theorem map.baseProjection.naturality.hom (P : B ⥤ᵖ B')
    {S T : Cospan B} (psi : S ⟶ T) :
    ((map.baseProjection P).naturality psi).hom =
      (ρ_ (P.map (Hom.base psi))).hom ≫
        (λ_ (P.map (Hom.base psi))).inv := sorry

/-- The inverse base-projection naturality cell is the reverse unitor composite on the mapped
base component. -/
@[simp]
theorem map.baseProjection.naturality.inv (P : B ⥤ᵖ B')
    {S T : Cospan B} (psi : S ⟶ T) :
    ((map.baseProjection P).naturality psi).inv =
      (λ_ (P.map (Hom.base psi))).hom ≫
        (ρ_ (P.map (Hom.base psi))).inv := sorry

/-- The chosen inverse component of the left-projection pointwise equivalence is the identity. -/
@[simp]
theorem map.leftProjection.pointwiseEquivalence.invApp
    (P : B ⥤ᵖ B') (S : Cospan B) :
    (map.leftProjection.pointwiseEquivalence P).invApp S =
      𝟙 (P.obj S.left) := sorry

/-- The chosen inverse component of the right-projection pointwise equivalence is the identity. -/
@[simp]
theorem map.rightProjection.pointwiseEquivalence.invApp
    (P : B ⥤ᵖ B') (S : Cospan B) :
    (map.rightProjection.pointwiseEquivalence P).invApp S =
      𝟙 (P.obj S.right) := sorry

/-- The chosen inverse component of the base-projection pointwise equivalence is the identity. -/
@[simp]
theorem map.baseProjection.pointwiseEquivalence.invApp
    (P : B ⥤ᵖ B') (S : Cospan B) :
    (map.baseProjection.pointwiseEquivalence P).invApp S =
      𝟙 (P.obj S.base) := sorry

end CategoryTheory.Bicategory.Cospan
