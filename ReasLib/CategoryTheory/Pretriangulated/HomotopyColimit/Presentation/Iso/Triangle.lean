module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Iso.Operations
import Mathlib.Tactic.CrossRefAttribute

/-!
# Triangle Isomorphisms from Telescope Presentations

A compatible isomorphism of telescope presentations canonically identifies their telescope
triangles.  The coproduct components directly reuse `ColimitCocone.Discrete.mapIso`, and their
forward and inverse maps are exposed for rewriting.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

universe u v

namespace CategoryTheory.HomotopyColimit.Presentation.Iso

open Limits.Sequential

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Naturality of the telescope map supplies the first square of the triangle isomorphism. -/
theorem triangleIso_comm₁ {S T : ℕ ⥤ D} {e : S ≅ T} {X Y : D}
    {P : HomotopyColimit.Presentation S X} {Q : HomotopyColimit.Presentation T Y}
    (Φ : HomotopyColimit.Presentation.Iso e P Q) :
    P.triangle.mor₁ ≫ (ColimitCocone.Discrete.mapIso P.coproduct Q.coproduct e.app).hom =
      (ColimitCocone.Discrete.mapIso P.coproduct Q.coproduct e.app).hom ≫ Q.triangle.mor₁ := sorry

/-- The coproduct-to-cocone square supplies the second square of the triangle isomorphism. -/
theorem triangleIso_comm₂ {S T : ℕ ⥤ D} {e : S ≅ T} {X Y : D}
    {P : HomotopyColimit.Presentation S X} {Q : HomotopyColimit.Presentation T Y}
    (Φ : HomotopyColimit.Presentation.Iso e P Q) :
    P.triangle.mor₂ ≫ Φ.iso.hom =
      (ColimitCocone.Discrete.mapIso P.coproduct Q.coproduct e.app).hom ≫ Q.triangle.mor₂ := sorry

/-- The connecting square supplies the third square of the triangle isomorphism. -/
theorem triangleIso_comm₃ {S T : ℕ ⥤ D} {e : S ≅ T} {X Y : D}
    {P : HomotopyColimit.Presentation S X} {Q : HomotopyColimit.Presentation T Y}
    (Φ : HomotopyColimit.Presentation.Iso e P Q) :
    P.triangle.mor₃ ≫
        (ColimitCocone.Discrete.mapIso P.coproduct Q.coproduct e.app).hom⟦(1 : ℤ)⟧' =
      Φ.iso.hom ≫ Q.triangle.mor₃ := sorry

/-- The canonical isomorphism of telescope triangles induced by a compatible isomorphism of
homotopy-colimit presentations. -/
@[stacks 0CRH]
def triangleIso {S T : ℕ ⥤ D} {e : S ≅ T} {X Y : D}
    {P : HomotopyColimit.Presentation S X} {Q : HomotopyColimit.Presentation T Y}
    (Φ : HomotopyColimit.Presentation.Iso e P Q) : P.triangle ≅ Q.triangle :=
  Triangle.isoMk P.triangle Q.triangle
    (ColimitCocone.Discrete.mapIso P.coproduct Q.coproduct e.app)
    (ColimitCocone.Discrete.mapIso P.coproduct Q.coproduct e.app) Φ.iso
    Φ.triangleIso_comm₁ Φ.triangleIso_comm₂ Φ.triangleIso_comm₃

/-- The first forward component of the induced triangle isomorphism is the explicit coproduct
map. -/
@[simp]
theorem triangleIso.hom₁ {S T : ℕ ⥤ D} {e : S ≅ T} {X Y : D}
    {P : HomotopyColimit.Presentation S X} {Q : HomotopyColimit.Presentation T Y}
    (Φ : HomotopyColimit.Presentation.Iso e P Q) :
    Φ.triangleIso.hom.hom₁ = ColimitCocone.Discrete.map P.coproduct Q.coproduct e.hom.app := sorry

/-- The second forward component of the induced triangle isomorphism is the same explicit
coproduct map. -/
@[simp]
theorem triangleIso.hom₂ {S T : ℕ ⥤ D} {e : S ≅ T} {X Y : D}
    {P : HomotopyColimit.Presentation S X} {Q : HomotopyColimit.Presentation T Y}
    (Φ : HomotopyColimit.Presentation.Iso e P Q) :
    Φ.triangleIso.hom.hom₂ = ColimitCocone.Discrete.map P.coproduct Q.coproduct e.hom.app := sorry

/-- The third forward component of the induced triangle isomorphism is the object
isomorphism. -/
@[simp]
theorem triangleIso.hom₃ {S T : ℕ ⥤ D} {e : S ≅ T} {X Y : D}
    {P : HomotopyColimit.Presentation S X} {Q : HomotopyColimit.Presentation T Y}
    (Φ : HomotopyColimit.Presentation.Iso e P Q) :
    Φ.triangleIso.hom.hom₃ = Φ.iso.hom := sorry

/-- The first inverse component of the induced triangle isomorphism is the inverse explicit
coproduct map. -/
@[simp]
theorem triangleIso.inv₁ {S T : ℕ ⥤ D} {e : S ≅ T} {X Y : D}
    {P : HomotopyColimit.Presentation S X} {Q : HomotopyColimit.Presentation T Y}
    (Φ : HomotopyColimit.Presentation.Iso e P Q) :
    Φ.triangleIso.inv.hom₁ = ColimitCocone.Discrete.map Q.coproduct P.coproduct e.inv.app := sorry

/-- The second inverse component of the induced triangle isomorphism is the same inverse
explicit coproduct map. -/
@[simp]
theorem triangleIso.inv₂ {S T : ℕ ⥤ D} {e : S ≅ T} {X Y : D}
    {P : HomotopyColimit.Presentation S X} {Q : HomotopyColimit.Presentation T Y}
    (Φ : HomotopyColimit.Presentation.Iso e P Q) :
    Φ.triangleIso.inv.hom₂ = ColimitCocone.Discrete.map Q.coproduct P.coproduct e.inv.app := sorry

/-- The third inverse component of the induced triangle isomorphism is the inverse object
isomorphism. -/
@[simp]
theorem triangleIso.inv₃ {S T : ℕ ⥤ D} {e : S ≅ T} {X Y : D}
    {P : HomotopyColimit.Presentation S X} {Q : HomotopyColimit.Presentation T Y}
    (Φ : HomotopyColimit.Presentation.Iso e P Q) :
    Φ.triangleIso.inv.hom₃ = Φ.iso.inv := sorry

/-- The forward map of the triangle isomorphism is the triangle morphism obtained by
forgetting invertibility. -/
@[simp]
theorem triangleIso_hom_eq_triangleMorphism
    {S T : ℕ ⥤ D} {e : S ≅ T} {X Y : D}
    {P : HomotopyColimit.Presentation S X} {Q : HomotopyColimit.Presentation T Y}
    (Φ : HomotopyColimit.Presentation.Iso e P Q) :
    Φ.triangleIso.hom = Φ.toHom.triangleMorphism := sorry

/-- The inverse map of the triangle isomorphism is the triangle morphism obtained from the
inverse presentation isomorphism. -/
@[simp]
theorem triangleIso_inv_eq_symmTriangleMorphism
    {S T : ℕ ⥤ D} {e : S ≅ T} {X Y : D}
    {P : HomotopyColimit.Presentation S X} {Q : HomotopyColimit.Presentation T Y}
    (Φ : HomotopyColimit.Presentation.Iso e P Q) :
    Φ.triangleIso.inv = Φ.symm.toHom.triangleMorphism := sorry

/-- The triangle isomorphism induced by the identity presentation isomorphism is the
identity. -/
@[simp]
theorem refl_triangleIso {S : ℕ ⥤ D} {X : D}
    (P : HomotopyColimit.Presentation S X) :
    (refl P).triangleIso = CategoryTheory.Iso.refl P.triangle := sorry

/-- The triangle isomorphism induced by an inverse presentation isomorphism is the inverse
triangle isomorphism. -/
@[simp]
theorem symm_triangleIso {S T : ℕ ⥤ D} {e : S ≅ T} {X Y : D}
    {P : HomotopyColimit.Presentation S X} {Q : HomotopyColimit.Presentation T Y}
    (Φ : HomotopyColimit.Presentation.Iso e P Q) :
    Φ.symm.triangleIso = Φ.triangleIso.symm := sorry

/-- The triangle isomorphism induced by a composite presentation isomorphism is the
composite triangle isomorphism. -/
@[simp]
theorem trans_triangleIso
    {S T U : ℕ ⥤ D} {e : S ≅ T} {f : T ≅ U} {X Y Z : D}
    {P : HomotopyColimit.Presentation S X} {Q : HomotopyColimit.Presentation T Y}
    {R : HomotopyColimit.Presentation U Z}
    (Φ : HomotopyColimit.Presentation.Iso e P Q)
    (Ψ : HomotopyColimit.Presentation.Iso f Q R) :
    (Φ.trans Ψ).triangleIso = Φ.triangleIso ≪≫ Ψ.triangleIso := sorry

end CategoryTheory.HomotopyColimit.Presentation.Iso
