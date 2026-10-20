module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Pseudofunctor.Construction
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Projection
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection comparisons for full-subbicategory two-fibre products

The comparison isomorphisms relating the selected two-fibre-product maps to the endpoint
projections of a bundled cospan.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open BasedCategory Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace TwoFibreProduct

variable
  {P : ObjectProperty
    (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable [BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder P]

/-- The first-projection comparison for the bundled full-subbicategory two-fibre-product
action. -/
@[stacks 0040 "first projection of a full-subbicategory two-fibre-product pseudofunctor"]
noncomputable def pseudofunctor.fstIso
    {S T : Bicategory.Cospan P.FullSubbicategory}
    (psi : S ⟶ T) :
    (pseudofunctor P).map psi ≫ fst T.fst T.snd ≅
      fst S.fst S.snd ≫ Bicategory.Cospan.Hom.left psi :=
  map.fstIso (Bicategory.Cospan.Hom.toCospanTransform psi)

/-- The bundled first-projection comparison is the comparison owned by the explicit
two-fibre-product map. -/
@[simp]
theorem pseudofunctor.fstIso_eq
    {S T : Bicategory.Cospan P.FullSubbicategory}
    (psi : S ⟶ T) :
    pseudofunctor.fstIso psi =
      map.fstIso (Bicategory.Cospan.Hom.toCospanTransform psi) := sorry

/-- The hom component of the bundled first-projection comparison. -/
@[simp]
theorem pseudofunctor.fstIso.hom
    {S T : Bicategory.Cospan P.FullSubbicategory}
    (psi : S ⟶ T) :
    (pseudofunctor.fstIso psi).hom =
      (map.fstIso (Bicategory.Cospan.Hom.toCospanTransform psi)).hom := sorry

/-- The inverse component of the bundled first-projection comparison. -/
@[simp]
theorem pseudofunctor.fstIso.inv
    {S T : Bicategory.Cospan P.FullSubbicategory}
    (psi : S ⟶ T) :
    (pseudofunctor.fstIso psi).inv =
      (map.fstIso (Bicategory.Cospan.Hom.toCospanTransform psi)).inv := sorry

/-- The second-projection comparison for the bundled full-subbicategory two-fibre-product
action. -/
@[stacks 0040 "second projection of a full-subbicategory two-fibre-product pseudofunctor"]
noncomputable def pseudofunctor.sndIso
    {S T : Bicategory.Cospan P.FullSubbicategory}
    (psi : S ⟶ T) :
    (pseudofunctor P).map psi ≫ snd T.fst T.snd ≅
      snd S.fst S.snd ≫ Bicategory.Cospan.Hom.right psi :=
  map.sndIso (Bicategory.Cospan.Hom.toCospanTransform psi)

/-- The bundled second-projection comparison is the comparison owned by the explicit
two-fibre-product map. -/
@[simp]
theorem pseudofunctor.sndIso_eq
    {S T : Bicategory.Cospan P.FullSubbicategory}
    (psi : S ⟶ T) :
    pseudofunctor.sndIso psi =
      map.sndIso (Bicategory.Cospan.Hom.toCospanTransform psi) := sorry

/-- The hom component of the bundled second-projection comparison. -/
@[simp]
theorem pseudofunctor.sndIso.hom
    {S T : Bicategory.Cospan P.FullSubbicategory}
    (psi : S ⟶ T) :
    (pseudofunctor.sndIso psi).hom =
      (map.sndIso (Bicategory.Cospan.Hom.toCospanTransform psi)).hom := sorry

/-- The inverse component of the bundled second-projection comparison. -/
@[simp]
theorem pseudofunctor.sndIso.inv
    {S T : Bicategory.Cospan P.FullSubbicategory}
    (psi : S ⟶ T) :
    (pseudofunctor.sndIso psi).inv =
      (map.sndIso (Bicategory.Cospan.Hom.toCospanTransform psi)).inv := sorry

end TwoFibreProduct

end CategoryTheory
