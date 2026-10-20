module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseAdjunction.Action.StrongTrans
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseAdjunction.Constructors

/-!
# Identity and composition coherence for pointwise adjunction actions

The action `PointwiseAdjunction.mapAdj` preserves the canonical pointwise
identity and composition operations up to componentwise mate isomorphisms.
This is the general comparison API used by mapped adjunctions between
pseudofunctors.
-/

@[expose] public section

universe wB vB uB wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor.StrongTrans.PointwiseAdjunction

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {D : Type uD} [Bicategory.{wD, vD} D]
variable {F G H : Pseudofunctor B D}

/-- The identity comparison has identity mate components. -/
private theorem mapAdj.idIso.appIso.conjugate
    (F : Pseudofunctor B D) (a : Bicategory.Adj B) :
    Bicategory.conjugateEquiv
        ((StrongTrans.id F.mapAdj).app a).adj
        (((id F).mapAdj).app a).adj
        (𝟙 _) =
      𝟙 _ := sorry

/-- The component comparison from the action of the pointwise identity adjunction to the
identity action. -/
@[stacks 0040 "component identity comparison for a pointwise adjunction action"]
def mapAdj.idIso.appIso
    (F : Pseudofunctor B D) (a : Bicategory.Adj B) :
    ((id F).mapAdj).app a ≅
      (StrongTrans.id F.mapAdj).app a :=
  Bicategory.Adj.iso₂Mk (Iso.refl _) (Iso.refl _)
    (mapAdj.idIso.appIso.conjugate F a)

/-- The forward left-adjoint component of the pointwise identity comparison. -/
@[simp]
theorem mapAdj.idIso.appIso.hom.τl
    (F : Pseudofunctor B D) (a : Bicategory.Adj B) :
    (mapAdj.idIso.appIso F a).hom.τl = 𝟙 _ := sorry

/-- The forward right-adjoint component of the pointwise identity comparison. -/
@[simp]
theorem mapAdj.idIso.appIso.hom.τr
    (F : Pseudofunctor B D) (a : Bicategory.Adj B) :
    (mapAdj.idIso.appIso F a).hom.τr = 𝟙 _ := sorry

/-- The inverse left-adjoint component of the pointwise identity comparison. -/
@[simp]
theorem mapAdj.idIso.appIso.inv.τl
    (F : Pseudofunctor B D) (a : Bicategory.Adj B) :
    (mapAdj.idIso.appIso F a).inv.τl = 𝟙 _ := sorry

/-- The inverse right-adjoint component of the pointwise identity comparison. -/
@[simp]
theorem mapAdj.idIso.appIso.inv.τr
    (F : Pseudofunctor B D) (a : Bicategory.Adj B) :
    (mapAdj.idIso.appIso F a).inv.τr = 𝟙 _ := sorry

/-- The pointwise identity comparisons satisfy modification naturality. -/
theorem mapAdj.idIso.naturality
    (F : Pseudofunctor B D) {a b : Bicategory.Adj B} (f : a ⟶ b) :
    F.mapAdj.map f ◁ (mapAdj.idIso.appIso F b).hom ≫
          ((StrongTrans.id F.mapAdj).naturality f).hom =
      (((id F).mapAdj).naturality f).hom ≫
        (mapAdj.idIso.appIso F a).hom ▷ F.mapAdj.map f := sorry

/-- The action of the canonical pointwise identity adjunction is isomorphic to the identity
strong transformation. -/
@[stacks 0040 "identity comparison for a pointwise adjunction action"]
def mapAdj.idIso (F : Pseudofunctor B D) :
    (id F).mapAdj ≅ 𝟙 F.mapAdj :=
  StrongTrans.isoMk
    (mapAdj.idIso.appIso F)
    (mapAdj.idIso.naturality F)

/-- The forward component of the identity comparison is its pointwise mate comparison. -/
@[simp]
theorem mapAdj.idIso.hom.app
    (F : Pseudofunctor B D) (a : Bicategory.Adj B) :
    (mapAdj.idIso F).hom.as.app a =
      (mapAdj.idIso.appIso F a).hom := sorry

/-- The inverse component of the identity comparison is its inverse pointwise mate
comparison. -/
@[simp]
theorem mapAdj.idIso.inv.app
    (F : Pseudofunctor B D) (a : Bicategory.Adj B) :
    (mapAdj.idIso F).inv.as.app a =
      (mapAdj.idIso.appIso F a).inv := sorry

/-- The composition comparison has identity mate components. -/
private theorem mapAdj.compIso.appIso.conjugate
    {η : F ⟶ G} {θ : G ⟶ H}
    (hη : PointwiseAdjunction η) (hθ : PointwiseAdjunction θ)
    (a : Bicategory.Adj B) :
    Bicategory.conjugateEquiv
        ((StrongTrans.vcomp hη.mapAdj hθ.mapAdj).app a).adj
        (((comp hη hθ).mapAdj).app a).adj
        (𝟙 _) =
      𝟙 _ := sorry

/-- The component comparison from the action of a composite pointwise adjunction to the
composite of the induced actions. -/
@[stacks 0040 "component composition comparison for pointwise adjunction actions"]
def mapAdj.compIso.appIso
    {η : F ⟶ G} {θ : G ⟶ H}
    (hη : PointwiseAdjunction η) (hθ : PointwiseAdjunction θ)
    (a : Bicategory.Adj B) :
    ((comp hη hθ).mapAdj).app a ≅
      (StrongTrans.vcomp hη.mapAdj hθ.mapAdj).app a :=
  Bicategory.Adj.iso₂Mk (Iso.refl _) (Iso.refl _)
    (mapAdj.compIso.appIso.conjugate hη hθ a)

/-- The forward left-adjoint component of the pointwise composition comparison. -/
@[simp]
theorem mapAdj.compIso.appIso.hom.τl
    {η : F ⟶ G} {θ : G ⟶ H}
    (hη : PointwiseAdjunction η) (hθ : PointwiseAdjunction θ)
    (a : Bicategory.Adj B) :
    (mapAdj.compIso.appIso hη hθ a).hom.τl = 𝟙 _ := sorry

/-- The forward right-adjoint component of the pointwise composition comparison. -/
@[simp]
theorem mapAdj.compIso.appIso.hom.τr
    {η : F ⟶ G} {θ : G ⟶ H}
    (hη : PointwiseAdjunction η) (hθ : PointwiseAdjunction θ)
    (a : Bicategory.Adj B) :
    (mapAdj.compIso.appIso hη hθ a).hom.τr = 𝟙 _ := sorry

/-- The inverse left-adjoint component of the pointwise composition comparison. -/
@[simp]
theorem mapAdj.compIso.appIso.inv.τl
    {η : F ⟶ G} {θ : G ⟶ H}
    (hη : PointwiseAdjunction η) (hθ : PointwiseAdjunction θ)
    (a : Bicategory.Adj B) :
    (mapAdj.compIso.appIso hη hθ a).inv.τl = 𝟙 _ := sorry

/-- The inverse right-adjoint component of the pointwise composition comparison. -/
@[simp]
theorem mapAdj.compIso.appIso.inv.τr
    {η : F ⟶ G} {θ : G ⟶ H}
    (hη : PointwiseAdjunction η) (hθ : PointwiseAdjunction θ)
    (a : Bicategory.Adj B) :
    (mapAdj.compIso.appIso hη hθ a).inv.τr = 𝟙 _ := sorry

/-- The pointwise composition comparisons satisfy modification naturality. -/
theorem mapAdj.compIso.naturality
    {η : F ⟶ G} {θ : G ⟶ H}
    (hη : PointwiseAdjunction η) (hθ : PointwiseAdjunction θ)
    {a b : Bicategory.Adj B} (f : a ⟶ b) :
    F.mapAdj.map f ◁
          (mapAdj.compIso.appIso hη hθ b).hom ≫
        ((StrongTrans.vcomp hη.mapAdj hθ.mapAdj).naturality f).hom =
      (((comp hη hθ).mapAdj).naturality f).hom ≫
        (mapAdj.compIso.appIso hη hθ a).hom ▷
          H.mapAdj.map f := sorry

/-- The action of a composite pointwise adjunction is isomorphic to the composite of its
two induced actions. -/
@[stacks 0040 "composition comparison for pointwise adjunction actions"]
def mapAdj.compIso
    {η : F ⟶ G} {θ : G ⟶ H}
    (hη : PointwiseAdjunction η) (hθ : PointwiseAdjunction θ) :
    (comp hη hθ).mapAdj ≅ StrongTrans.vcomp hη.mapAdj hθ.mapAdj :=
  StrongTrans.isoMk
    (mapAdj.compIso.appIso hη hθ)
    (mapAdj.compIso.naturality hη hθ)

/-- The forward component of the composition comparison is its pointwise mate
comparison. -/
@[simp]
theorem mapAdj.compIso.hom.app
    {η : F ⟶ G} {θ : G ⟶ H}
    (hη : PointwiseAdjunction η) (hθ : PointwiseAdjunction θ)
    (a : Bicategory.Adj B) :
    (mapAdj.compIso hη hθ).hom.as.app a =
      (mapAdj.compIso.appIso hη hθ a).hom := sorry

/-- The inverse component of the composition comparison is its inverse pointwise mate
comparison. -/
@[simp]
theorem mapAdj.compIso.inv.app
    {η : F ⟶ G} {θ : G ⟶ H}
    (hη : PointwiseAdjunction η) (hθ : PointwiseAdjunction θ)
    (a : Bicategory.Adj B) :
    (mapAdj.compIso hη hθ).inv.as.app a =
      (mapAdj.compIso.appIso hη hθ a).inv := sorry

/- Data audit (mathlib 4.32): both comparison isomorphisms are assembled
from explicit identity mate components; `sorryAx` occurs only in mate and
modification coherence fields. -/

end Pseudofunctor.StrongTrans.PointwiseAdjunction

end CategoryTheory
