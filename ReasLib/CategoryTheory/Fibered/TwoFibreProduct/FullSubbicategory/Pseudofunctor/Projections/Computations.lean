module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Pseudofunctor.Projections.Construction

/-!
# Computations for full-subbicategory two-fibre-product projections

Object and naturality readouts for the two canonical projection transformations.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open BasedCategory Bicategory ObjectProperty

variable {C : Type u} [Category.{v} C]

namespace TwoFibreProduct

variable
  {P : ObjectProperty
    (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable [BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder P]

/-- The object component of the canonical first-projection strong transformation is the
explicit selected first projection. -/
@[simp]
theorem pseudofunctor.fst.app
    (S : Bicategory.Cospan P.FullSubbicategory) :
    (pseudofunctor.fst P).app S =
      _root_.CategoryTheory.TwoFibreProduct.fst S.fst S.snd := sorry

/-- The naturality isomorphism of the canonical first-projection transformation is the
selected first-projection comparison. -/
@[simp]
theorem pseudofunctor.fst.naturality
    {S T : Bicategory.Cospan P.FullSubbicategory} (psi : S ⟶ T) :
    (pseudofunctor.fst P).naturality psi = pseudofunctor.fstIso psi := sorry

/-- The hom component of first-projection naturality is the selected comparison hom. -/
@[simp]
theorem pseudofunctor.fst.naturality.hom
    {S T : Bicategory.Cospan P.FullSubbicategory} (psi : S ⟶ T) :
    ((pseudofunctor.fst P).naturality psi).hom =
      (pseudofunctor.fstIso psi).hom := sorry

/-- The inverse component of first-projection naturality is the selected comparison inverse. -/
@[simp]
theorem pseudofunctor.fst.naturality.inv
    {S T : Bicategory.Cospan P.FullSubbicategory} (psi : S ⟶ T) :
    ((pseudofunctor.fst P).naturality psi).inv =
      (pseudofunctor.fstIso psi).inv := sorry

/-- The object component of the canonical second-projection strong transformation is the
explicit selected second projection. -/
@[simp]
theorem pseudofunctor.snd.app
    (S : Bicategory.Cospan P.FullSubbicategory) :
    (pseudofunctor.snd P).app S =
      _root_.CategoryTheory.TwoFibreProduct.snd S.fst S.snd := sorry

/-- The naturality isomorphism of the canonical second-projection transformation is the
selected second-projection comparison. -/
@[simp]
theorem pseudofunctor.snd.naturality
    {S T : Bicategory.Cospan P.FullSubbicategory} (psi : S ⟶ T) :
    (pseudofunctor.snd P).naturality psi = pseudofunctor.sndIso psi := sorry

/-- The hom component of second-projection naturality is the selected comparison hom. -/
@[simp]
theorem pseudofunctor.snd.naturality.hom
    {S T : Bicategory.Cospan P.FullSubbicategory} (psi : S ⟶ T) :
    ((pseudofunctor.snd P).naturality psi).hom =
      (pseudofunctor.sndIso psi).hom := sorry

/-- The inverse component of second-projection naturality is the selected comparison inverse. -/
@[simp]
theorem pseudofunctor.snd.naturality.inv
    {S T : Bicategory.Cospan P.FullSubbicategory} (psi : S ⟶ T) :
    ((pseudofunctor.snd P).naturality psi).inv =
      (pseudofunctor.sndIso psi).inv := sorry

end TwoFibreProduct

end CategoryTheory
