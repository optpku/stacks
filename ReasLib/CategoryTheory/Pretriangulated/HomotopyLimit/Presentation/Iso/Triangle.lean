module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Iso.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Triangle Isomorphisms from Homotopy-Limit Presentations

A compatible isomorphism of presentations canonically identifies the corresponding Milnor
triangles.  The forward and inverse components are exposed for downstream rewriting; the
product component directly reuses `ProductCone.mapIso`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

universe u v

namespace CategoryTheory.HomotopyLimit.Presentation.Iso

open SequentialInverseSystem.Milnor

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The first square needed for the triangle isomorphism associated to a presentation
isomorphism. -/
theorem triangleIso_comm₁
    {K L : SequentialInverseSystem D} {e : K ≅ L} {X Y : D}
    {P : HomotopyLimit.Presentation K X} {Q : HomotopyLimit.Presentation L Y}
    (Φ : HomotopyLimit.Presentation.Iso e P Q) :
    P.triangle.mor₁ ≫ (ProductCone.mapIso P.product Q.product e).hom =
      Φ.iso.hom ≫ Q.triangle.mor₁ := sorry

/-- Naturality of the Milnor difference supplies the middle square of the triangle
isomorphism associated to a presentation isomorphism. -/
theorem triangleIso_comm₂
    {K L : SequentialInverseSystem D} {e : K ≅ L} {X Y : D}
    {P : HomotopyLimit.Presentation K X} {Q : HomotopyLimit.Presentation L Y}
    (Φ : HomotopyLimit.Presentation.Iso e P Q) :
    P.triangle.mor₂ ≫ (ProductCone.mapIso P.product Q.product e).hom =
      (ProductCone.mapIso P.product Q.product e).hom ≫ Q.triangle.mor₂ := sorry

/-- The connecting square needed for the triangle isomorphism associated to a presentation
isomorphism. -/
theorem triangleIso_comm₃
    {K L : SequentialInverseSystem D} {e : K ≅ L} {X Y : D}
    {P : HomotopyLimit.Presentation K X} {Q : HomotopyLimit.Presentation L Y}
    (Φ : HomotopyLimit.Presentation.Iso e P Q) :
    P.triangle.mor₃ ≫ Φ.iso.hom⟦(1 : ℤ)⟧' =
      (ProductCone.mapIso P.product Q.product e).hom ≫ Q.triangle.mor₃ := sorry

/-- The canonical isomorphism of Milnor triangles induced by a compatible isomorphism of
homotopy-limit presentations. -/
@[stacks 08TC]
def triangleIso
    {K L : SequentialInverseSystem D} {e : K ≅ L} {X Y : D}
    {P : HomotopyLimit.Presentation K X} {Q : HomotopyLimit.Presentation L Y}
    (Φ : HomotopyLimit.Presentation.Iso e P Q) : P.triangle ≅ Q.triangle :=
  Triangle.isoMk P.triangle Q.triangle Φ.iso
    (ProductCone.mapIso P.product Q.product e)
    (ProductCone.mapIso P.product Q.product e)
    Φ.triangleIso_comm₁ Φ.triangleIso_comm₂ Φ.triangleIso_comm₃

/-- The first forward component of the induced triangle isomorphism is the object
isomorphism. -/
@[simp]
theorem triangleIso.hom₁
    {K L : SequentialInverseSystem D} {e : K ≅ L} {X Y : D}
    {P : HomotopyLimit.Presentation K X} {Q : HomotopyLimit.Presentation L Y}
    (Φ : HomotopyLimit.Presentation.Iso e P Q) :
    Φ.triangleIso.hom.hom₁ = Φ.iso.hom := sorry

/-- The second forward component of the induced triangle isomorphism is the product map. -/
@[simp]
theorem triangleIso.hom₂
    {K L : SequentialInverseSystem D} {e : K ≅ L} {X Y : D}
    {P : HomotopyLimit.Presentation K X} {Q : HomotopyLimit.Presentation L Y}
    (Φ : HomotopyLimit.Presentation.Iso e P Q) :
    Φ.triangleIso.hom.hom₂ =
      ProductCone.map P.product Q.product e.hom := sorry

/-- The third forward component of the induced triangle isomorphism is the product map. -/
@[simp]
theorem triangleIso.hom₃
    {K L : SequentialInverseSystem D} {e : K ≅ L} {X Y : D}
    {P : HomotopyLimit.Presentation K X} {Q : HomotopyLimit.Presentation L Y}
    (Φ : HomotopyLimit.Presentation.Iso e P Q) :
    Φ.triangleIso.hom.hom₃ =
      ProductCone.map P.product Q.product e.hom := sorry

/-- The first inverse component of the induced triangle isomorphism is the inverse object
isomorphism. -/
@[simp]
theorem triangleIso.inv₁
    {K L : SequentialInverseSystem D} {e : K ≅ L} {X Y : D}
    {P : HomotopyLimit.Presentation K X} {Q : HomotopyLimit.Presentation L Y}
    (Φ : HomotopyLimit.Presentation.Iso e P Q) :
    Φ.triangleIso.inv.hom₁ = Φ.iso.inv := sorry

/-- The second inverse component of the induced triangle isomorphism is the inverse product
map. -/
@[simp]
theorem triangleIso.inv₂
    {K L : SequentialInverseSystem D} {e : K ≅ L} {X Y : D}
    {P : HomotopyLimit.Presentation K X} {Q : HomotopyLimit.Presentation L Y}
    (Φ : HomotopyLimit.Presentation.Iso e P Q) :
    Φ.triangleIso.inv.hom₂ =
      ProductCone.map Q.product P.product e.inv := sorry

/-- The third inverse component of the induced triangle isomorphism is the inverse product
map. -/
@[simp]
theorem triangleIso.inv₃
    {K L : SequentialInverseSystem D} {e : K ≅ L} {X Y : D}
    {P : HomotopyLimit.Presentation K X} {Q : HomotopyLimit.Presentation L Y}
    (Φ : HomotopyLimit.Presentation.Iso e P Q) :
    Φ.triangleIso.inv.hom₃ =
      ProductCone.map Q.product P.product e.inv := sorry

end CategoryTheory.HomotopyLimit.Presentation.Iso
