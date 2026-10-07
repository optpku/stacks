module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Pseudofunctor.Construction.Basic

/-!
# Action of the full-subbicategory two-fibre-product pseudofunctor

Direct readouts of its object, `1`-cell, `2`-cell, comparison, and hom-functor actions.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open BasedCategory Bicategory ObjectProperty
open scoped Bicategory Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]

namespace TwoFibreProduct

variable
  {P : ObjectProperty
    (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable [BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder P]

/-- The object action of the full-subbicategory two-fibre-product pseudofunctor is the explicit
selected apex. -/
@[simp]
theorem pseudofunctor.obj
    (S : Bicategory.Cospan P.FullSubbicategory) :
    (pseudofunctor P).obj S = apex S.fst S.snd := sorry

/-- The `1`-cell action of the full-subbicategory two-fibre-product pseudofunctor is the
existing componentwise map. -/
@[simp]
theorem pseudofunctor.map
    {S T : Bicategory.Cospan P.FullSubbicategory}
    (psi : S ⟶ T) :
    (pseudofunctor P).map psi =
      map (Bicategory.Cospan.Hom.toCospanTransform psi) := sorry

/-- The `2`-cell action of the full-subbicategory two-fibre-product pseudofunctor is the
existing locally full transformation. -/
@[simp]
theorem pseudofunctor.map₂
    {S T : Bicategory.Cospan P.FullSubbicategory}
    {psi phi : S ⟶ T} (Gamma : psi ⟶ phi) :
    (pseudofunctor P).map₂ Gamma =
      map₂ (Bicategory.Cospan.Hom₂.toModification Gamma) := sorry

/-- The identity comparison of the full-subbicategory two-fibre-product pseudofunctor is the
explicit identity comparison. -/
@[simp]
theorem pseudofunctor.mapId
    (S : Bicategory.Cospan P.FullSubbicategory) :
    (pseudofunctor P).mapId S = map.idIso S.fst S.snd := sorry

/-- The composition comparison of the full-subbicategory two-fibre-product pseudofunctor is
the explicit composition comparison. -/
@[simp]
theorem pseudofunctor.mapComp
    {R S T : Bicategory.Cospan P.FullSubbicategory}
    (psi : R ⟶ S) (phi : S ⟶ T) :
    (pseudofunctor P).mapComp psi phi =
      map.compIso
        (Bicategory.Cospan.Hom.toCospanTransform psi)
        (Bicategory.Cospan.Hom.toCospanTransform phi) := sorry

/-- On each hom category, the two-fibre-product pseudofunctor is the computational hom functor
after exposing bundled cospan transformations. -/
@[simp]
theorem pseudofunctor.mapFunctor
    (S T : Bicategory.Cospan P.FullSubbicategory) :
    (pseudofunctor P).mapFunctor S T =
      (Bicategory.Cospan.inclusion
        (B := P.FullSubbicategory)).mapFunctor S T ⋙
        mapFunctor (F₁ := S.fst) (G₁ := S.snd)
          (F₂ := T.fst) (G₂ := T.snd) := sorry

end TwoFibreProduct

end CategoryTheory
