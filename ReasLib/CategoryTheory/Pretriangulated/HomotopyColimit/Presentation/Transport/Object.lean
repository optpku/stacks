module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Object Transport of Homotopy-Colimit Presentations

This leaf transports a telescope presentation along an isomorphism of its presented object.
The explicit coproduct cocone is retained unchanged.
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

/-- The coproduct-to-cocone map after replacing the presented object by an isomorphic
object. -/
def toCocone {K : ℕ ⥤ D} {X Y : D} (P : Presentation K X) (e : X ≅ Y) :
    P.coproduct.cocone.pt ⟶ Y :=
  P.toCocone ≫ e.hom

/-- The connecting morphism after replacing the presented object by an isomorphic object. -/
def connecting {K : ℕ ⥤ D} {X Y : D} (P : Presentation K X) (e : X ≅ Y) :
    Y ⟶ P.coproduct.cocone.pt⟦(1 : ℤ)⟧ :=
  e.inv ≫ P.connecting

/-- Replacing the presented object by an isomorphic object preserves distinguishedness of
the telescope triangle. -/
@[stacks 090Z]
theorem distinguished {K : ℕ ⥤ D} {X Y : D}
    (P : Presentation K X) (e : X ≅ Y) :
    Triangle.mk (CoproductCocone.telescopeMap K P.coproduct)
      (toCocone P e) (connecting P e) ∈ distTriang D := sorry

end Presentation.ObjectIso

/-- Transport a telescope presentation along an isomorphism of its presented object while
retaining the explicit coproduct cocone. -/
@[stacks 090Z]
def Presentation.ofObjectIso {K : ℕ ⥤ D} {X Y : D}
    (P : Presentation K X) (e : X ≅ Y) : Presentation K Y where
  coproduct := P.coproduct
  toCocone := ObjectIso.toCocone P e
  connecting := ObjectIso.connecting P e
  distinguished := ObjectIso.distinguished P e

/-- Object transport retains the explicit coproduct cocone. -/
@[simp]
theorem Presentation.ofObjectIso.coproduct {K : ℕ ⥤ D} {X Y : D}
    (P : Presentation K X) (e : X ≅ Y) :
    (P.ofObjectIso e).coproduct = P.coproduct := sorry

/-- The coproduct-to-cocone map after object transport is postcomposed with the forward
isomorphism. -/
@[simp]
theorem Presentation.ofObjectIso.toCocone {K : ℕ ⥤ D} {X Y : D}
    (P : Presentation K X) (e : X ≅ Y) :
    (P.ofObjectIso e).toCocone = P.toCocone ≫ e.hom := sorry

/-- The connecting map after object transport is precomposed with the inverse isomorphism. -/
@[simp]
theorem Presentation.ofObjectIso.connecting {K : ℕ ⥤ D} {X Y : D}
    (P : Presentation K X) (e : X ≅ Y) :
    (P.ofObjectIso e).connecting = e.inv ≫ P.connecting := sorry

/-- Every stage map after object transport is postcomposed with the forward isomorphism. -/
@[simp, reassoc]
theorem Presentation.ofObjectIso.ι {K : ℕ ⥤ D} {X Y : D}
    (P : Presentation K X) (e : X ≅ Y) (n : ℕ) :
    (P.ofObjectIso e).ι n = P.ι n ≫ e.hom := sorry

/-- The cocone legs after object transport are postcomposed with the forward isomorphism. -/
@[simp, reassoc]
theorem Presentation.ofObjectIso.cocone_ι_app {K : ℕ ⥤ D} {X Y : D}
    (P : Presentation K X) (e : X ≅ Y) (n : ℕ) :
    (P.ofObjectIso e).cocone.ι.app n = P.cocone.ι.app n ≫ e.hom := sorry

/-- Transporting a presentation along the identity isomorphism recovers the original
presentation. -/
@[simp]
theorem Presentation.ofObjectIso.refl {K : ℕ ⥤ D} {X : D}
    (P : Presentation K X) :
    P.ofObjectIso (CategoryTheory.Iso.refl X) = P := sorry

/-- Successive object transports agree with transport along the composite isomorphism. -/
@[simp]
theorem Presentation.ofObjectIso.trans {K : ℕ ⥤ D} {X Y Z : D}
    (P : Presentation K X) (e : X ≅ Y) (f : Y ≅ Z) :
    (P.ofObjectIso e).ofObjectIso f = P.ofObjectIso (e ≪≫ f) := sorry

namespace IsOf

/-- The homotopy-colimit predicate is stable under an isomorphism of its candidate object. -/
@[stacks 0CRH]
theorem ofObjectIso {K : ℕ ⥤ D} {X Y : D}
    (h : HomotopyColimit.IsOf K X) (e : X ≅ Y) :
    HomotopyColimit.IsOf K Y := sorry

end IsOf

end CategoryTheory.HomotopyColimit
