module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Transport.Object
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Transport.Diagram
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Iso
import Mathlib.Tactic.CrossRefAttribute

/-!
# Compatible Isomorphisms from Transported Homotopy-Colimit Presentations

Object and diagram transport canonically produce compatible `Presentation.Iso` data, exposing
the common stage, cocone, and triangle APIs of presentation isomorphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

universe u v

namespace CategoryTheory.HomotopyColimit

open Limits.Sequential

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

namespace Presentation.ObjectIso

/-- Coproduct-to-cocone compatibility for the presentation isomorphism induced by object
transport. -/
theorem presentationIso_toCoconeComm {K : ℕ ⥤ D} {X Y : D}
    (P : Presentation K X) (e : X ≅ Y) :
    CommSq P.toCocone
      (ColimitCocone.Discrete.map P.coproduct (P.ofObjectIso e).coproduct
        (𝟙 K : K ⟶ K).app)
      e.hom (P.ofObjectIso e).toCocone := sorry

/-- Connecting-map compatibility for the presentation isomorphism induced by object
transport. -/
theorem presentationIso_connectingComm {K : ℕ ⥤ D} {X Y : D}
    (P : Presentation K X) (e : X ≅ Y) :
    CommSq P.connecting e.hom
      ((ColimitCocone.Discrete.map P.coproduct
        (P.ofObjectIso e).coproduct (𝟙 K : K ⟶ K).app)⟦(1 : ℤ)⟧')
      (P.ofObjectIso e).connecting := sorry

/-- Object transport canonically yields a compatible isomorphism from the original
presentation to the transported presentation. -/
@[stacks 0CRH]
def presentationIso {K : ℕ ⥤ D} {X Y : D}
    (P : Presentation K X) (e : X ≅ Y) :
    Presentation.Iso (CategoryTheory.Iso.refl K) P (P.ofObjectIso e) where
  iso := e
  toCoconeComm := presentationIso_toCoconeComm P e
  connectingComm := presentationIso_connectingComm P e

/-- The object component of the compatible isomorphism induced by object transport is the
supplied isomorphism. -/
@[simp]
theorem presentationIso_iso {K : ℕ ⥤ D} {X Y : D}
    (P : Presentation K X) (e : X ≅ Y) :
    (presentationIso P e).iso = e := sorry

end Presentation.ObjectIso

namespace Presentation.DiagramIso

/-- Coproduct-to-cocone compatibility for the presentation isomorphism induced by diagram
transport. -/
theorem presentationIso_toCoconeComm {K L : ℕ ⥤ D} {X : D}
    (P : Presentation K X) (e : K ≅ L)
    (Q : ColimitCocone (Discrete.functor L.obj)) :
    CommSq P.toCocone
      (ColimitCocone.Discrete.map P.coproduct (P.ofDiagramIso e Q).coproduct e.hom.app)
      (𝟙 X) (P.ofDiagramIso e Q).toCocone := sorry

/-- Connecting-map compatibility for the presentation isomorphism induced by diagram
transport. -/
theorem presentationIso_connectingComm {K L : ℕ ⥤ D} {X : D}
    (P : Presentation K X) (e : K ≅ L)
    (Q : ColimitCocone (Discrete.functor L.obj)) :
    CommSq P.connecting (𝟙 X)
      ((ColimitCocone.Discrete.map P.coproduct
        (P.ofDiagramIso e Q).coproduct e.hom.app)⟦(1 : ℤ)⟧')
      (P.ofDiagramIso e Q).connecting := sorry

/-- Diagram transport canonically yields a compatible presentation isomorphism whose object
component is the identity. -/
@[stacks 0CRH]
def presentationIso {K L : ℕ ⥤ D} {X : D}
    (P : Presentation K X) (e : K ≅ L)
    (Q : ColimitCocone (Discrete.functor L.obj)) :
    Presentation.Iso e P (P.ofDiagramIso e Q) where
  iso := CategoryTheory.Iso.refl X
  toCoconeComm := presentationIso_toCoconeComm P e Q
  connectingComm := presentationIso_connectingComm P e Q

/-- The object component of the compatible isomorphism induced by diagram transport is the
identity isomorphism. -/
@[simp]
theorem presentationIso_iso {K L : ℕ ⥤ D} {X : D}
    (P : Presentation K X) (e : K ≅ L)
    (Q : ColimitCocone (Discrete.functor L.obj)) :
    (presentationIso P e Q).iso = CategoryTheory.Iso.refl X := sorry

namespace Selected

/-- Selected diagram transport canonically yields a compatible presentation isomorphism
without requiring an explicit target coproduct cocone. -/
@[stacks 0CRH]
def presentationIso {K L : ℕ ⥤ D} [HasCoproduct L.obj] {X : D}
    (P : Presentation K X) (e : K ≅ L) :
    Presentation.Iso e P (Presentation.DiagramIso.Selected.transport P e) :=
  Presentation.DiagramIso.presentationIso P e
    (getColimitCocone (Discrete.functor L.obj))

/-- The object component of the compatible isomorphism induced by selected diagram transport
is the identity isomorphism. -/
@[simp]
theorem presentationIso.iso {K L : ℕ ⥤ D} [HasCoproduct L.obj] {X : D}
    (P : Presentation K X) (e : K ≅ L) :
    (presentationIso P e).iso = CategoryTheory.Iso.refl X := sorry

end Selected

end Presentation.DiagramIso

end CategoryTheory.HomotopyColimit
