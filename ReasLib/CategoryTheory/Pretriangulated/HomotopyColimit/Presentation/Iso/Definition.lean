module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Morphism.Iso.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Definition of Isomorphisms of Telescope Presentations

This leaf specializes invertible maps of explicit telescope presentations to the forward map
of an isomorphism of sequential diagrams.  Compatibility is exposed on the retained
coproduct cocones and on every canonical stage map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

universe u v

namespace CategoryTheory.HomotopyColimit

open Limits.Sequential

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- An isomorphism between telescope presentations over an isomorphism of their sequential
diagrams, as an invertible presentation map over the forward diagram morphism. -/
@[stacks 0CRH "isomorphism of homotopy-colimit presentations"]
abbrev Presentation.Iso {S T : ℕ ⥤ D} (e : S ≅ T)
    {X Y : D} (P : Presentation S X) (Q : Presentation T Y) :=
  Presentation.HomWithIso e.hom P Q

namespace Presentation.Iso

/-- Forget invertibility from a compatible isomorphism of telescope presentations. -/
def toHom {S T : ℕ ⥤ D} {e : S ≅ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y}
    (Φ : Presentation.Iso e P Q) : Presentation.Hom e.hom P Q :=
  Presentation.HomWithIso.toHom Φ

/-- The underlying map after forgetting invertibility is the forward object isomorphism. -/
@[simp]
theorem toHom_hom {S T : ℕ ⥤ D} {e : S ≅ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y}
    (Φ : Presentation.Iso e P Q) : Φ.toHom.hom = Φ.iso.hom := sorry

/-- Compatibility of a presentation isomorphism with the coproduct-to-cocone maps. -/
@[reassoc]
theorem toCocone_naturality {S T : ℕ ⥤ D} {e : S ≅ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y}
    (Φ : Presentation.Iso e P Q) :
    P.toCocone ≫ Φ.iso.hom =
      ColimitCocone.Discrete.map P.coproduct Q.coproduct e.hom.app ≫ Q.toCocone := sorry

/-- Compatibility of a presentation isomorphism with the connecting maps. -/
@[reassoc]
theorem connecting_naturality {S T : ℕ ⥤ D} {e : S ≅ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y}
    (Φ : Presentation.Iso e P Q) :
    P.connecting ≫
        (ColimitCocone.Discrete.map P.coproduct Q.coproduct e.hom.app)⟦(1 : ℤ)⟧' =
      Φ.iso.hom ≫ Q.connecting := sorry

/-- A presentation isomorphism commutes with every canonical stage map. -/
@[reassoc, stacks 0CRH]
theorem ι_naturality {S T : ℕ ⥤ D} {e : S ≅ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y}
    (Φ : Presentation.Iso e P Q) (n : ℕ) :
    P.ι n ≫ Φ.iso.hom = e.hom.app n ≫ Q.ι n := sorry

end Presentation.Iso

end CategoryTheory.HomotopyColimit
