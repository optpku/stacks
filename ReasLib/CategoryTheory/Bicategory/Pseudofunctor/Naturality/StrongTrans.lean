module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Evaluation.At.Basic

/-!
# Component API for strong transformations

Evaluation of isomorphisms between strong transformations and objectwise coherence formulas.
-/

@[expose] public section

universe wB vB uB wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor.StrongTrans

variable {B : Type uB} [Bicategory.{wB, vB} B]

section IsoApp

variable {D : Type uD} [Bicategory.{wD, vD} D]
variable {F G : Pseudofunctor B D}

/-- Evaluate an isomorphism between strong transformations at an object of the source
bicategory. This is the modification-level analogue of `NatIso.app`. -/
def isoApp {η θ : F ⟶ G} (e : η ≅ θ) (a : B) :
    η.app a ≅ θ.app a :=
  (Pseudofunctor.evaluationHom a F G).mapIso e

/-- The forward and inverse components of an isomorphism between strong transformations cancel
at every object. -/
theorem isoApp.hom_inv_id
    {η θ : F ⟶ G} (e : η ≅ θ) (a : B) :
    e.hom.as.app a ≫ e.inv.as.app a = 𝟙 (η.app a) := sorry

/-- The inverse and forward components of an isomorphism between strong transformations cancel
at every object. -/
theorem isoApp.inv_hom_id
    {η θ : F ⟶ G} (e : η ≅ θ) (a : B) :
    e.inv.as.app a ≫ e.hom.as.app a = 𝟙 (θ.app a) := sorry

/-- The forward map of `isoApp` is the corresponding component of the forward modification. -/
@[simp]
theorem isoApp.hom
    {η θ : F ⟶ G} (e : η ≅ θ) (a : B) :
    (isoApp e a).hom = e.hom.as.app a := sorry

/-- The inverse map of `isoApp` is the corresponding component of the inverse modification. -/
@[simp]
theorem isoApp.inv
    {η θ : F ⟶ G} (e : η ≅ θ) (a : B) :
    (isoApp e a).inv = e.inv.as.app a := sorry

/-- Evaluation sends the identity isomorphism of a strong transformation to the identity
component isomorphism. -/
@[simp]
theorem isoApp.refl (η : F ⟶ G) (a : B) :
    isoApp (Iso.refl η) a = Iso.refl (η.app a) := sorry

/-- Evaluation commutes with symmetry of strong-transformation isomorphisms. -/
@[simp]
theorem isoApp.symm
    {η θ : F ⟶ G} (e : η ≅ θ) (a : B) :
    isoApp e.symm a = (isoApp e a).symm := sorry

/-- Evaluation commutes with composition of strong-transformation isomorphisms. -/
@[simp]
theorem isoApp.trans
    {η θ ι : F ⟶ G} (e : η ≅ θ) (e' : θ ≅ ι) (a : B) :
    isoApp (e ≪≫ e') a = isoApp e a ≪≫ isoApp e' a := sorry

end IsoApp

section CatNaturality

variable {F G : Pseudofunctor B Cat.{vD, uD}}

/-- Objectwise cancellation form of strong-transformation composition coherence using inverse
naturality components. -/
theorem mapComp.hom_naturality_inv_app
    (α : F ⟶ G) {a b c : B} (f : a ⟶ b) (g : b ⟶ c)
    (X : F.obj a) :
    (G.mapComp f g).hom.toNatTrans.app ((α.app a).toFunctor.obj X) ≫
        (G.map g).toFunctor.map ((α.naturality f).inv.toNatTrans.app X) ≫
        (α.naturality g).inv.toNatTrans.app ((F.map f).toFunctor.obj X) =
      (α.naturality (f ≫ g)).inv.toNatTrans.app X ≫
        (α.app c).toFunctor.map ((F.mapComp f g).hom.toNatTrans.app X) := sorry

/-- Objectwise cancellation form of strong-transformation composition coherence using forward
naturality components and the inverse composition comparison. -/
theorem naturality.hom_mapComp_inv_app
    (α : F ⟶ G) {a b c : B} (f : a ⟶ b) (g : b ⟶ c)
    (X : F.obj a) :
    (α.naturality g).hom.toNatTrans.app ((F.map f).toFunctor.obj X) ≫
        (G.map g).toFunctor.map ((α.naturality f).hom.toNatTrans.app X) ≫
        (G.mapComp f g).inv.toNatTrans.app ((α.app a).toFunctor.obj X) =
      (α.app c).toFunctor.map ((F.mapComp f g).inv.toNatTrans.app X) ≫
        (α.naturality (f ≫ g)).hom.toNatTrans.app X := sorry

end CatNaturality

end Pseudofunctor.StrongTrans

end CategoryTheory
