/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Morphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphisms of Homotopy-Limit Presentations

This leaf packages an isomorphism of inverse systems together with compatible isomorphisms
of their explicit Milnor presentations.  The compatibility is exposed both at the product
term and at every stage of the inverse systems.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

noncomputable section

universe u v

namespace CategoryTheory.HomotopyLimit

open SequentialInverseSystem.Milnor

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- An isomorphism between presentations over an isomorphism of their sequential inverse
systems.  It retains the object isomorphism and both squares of the induced Milnor triangle
morphism. -/
@[stacks 08TC "isomorphism of homotopy-limit presentations"]
structure Presentation.Iso {K L : SequentialInverseSystem D} (e : K ≅ L)
    {X Y : D} (P : Presentation K X) (Q : Presentation L Y) where
  /-- The isomorphism between the presented homotopy-limit objects. -/
  iso : X ≅ Y
  /-- The presentation inclusions commute with the map of explicit product cones. -/
  ιComm :
    CommSq P.ι iso.hom (ProductCone.map P.product Q.product e.hom) Q.ι
  /-- The presentation connecting morphisms commute with the map of explicit product cones
  and the shifted object isomorphism. -/
  connectingComm :
    CommSq P.connecting (ProductCone.map P.product Q.product e.hom)
      (iso.hom⟦(1 : ℤ)⟧') Q.connecting

namespace Presentation.Iso

/-- Forget invertibility from a compatible isomorphism of homotopy-limit presentations. -/
def toHom {K L : SequentialInverseSystem D} {e : K ≅ L} {X Y : D}
    {P : Presentation K X} {Q : Presentation L Y}
    (Φ : Presentation.Iso e P Q) : Presentation.Hom e.hom P Q where
  hom := Φ.iso.hom
  ιComm := Φ.ιComm
  connectingComm := Φ.connectingComm

/-- The underlying map after forgetting invertibility is the forward object isomorphism. -/
@[simp]
theorem toHom_hom {K L : SequentialInverseSystem D} {e : K ≅ L} {X Y : D}
    {P : Presentation K X} {Q : Presentation L Y}
    (Φ : Presentation.Iso e P Q) : Φ.toHom.hom = Φ.iso.hom := sorry

/-- Inclusion compatibility of a presentation isomorphism as a morphism equation. -/
@[reassoc]
theorem ι_naturality {K L : SequentialInverseSystem D} {e : K ≅ L} {X Y : D}
    {P : Presentation K X} {Q : Presentation L Y}
    (Φ : Presentation.Iso e P Q) :
    P.ι ≫ ProductCone.map P.product Q.product e.hom = Φ.iso.hom ≫ Q.ι := sorry

/-- Connecting compatibility of a presentation isomorphism as a morphism equation. -/
@[reassoc]
theorem connecting_naturality
    {K L : SequentialInverseSystem D} {e : K ≅ L} {X Y : D}
    {P : Presentation K X} {Q : Presentation L Y}
    (Φ : Presentation.Iso e P Q) :
    P.connecting ≫ Φ.iso.hom⟦(1 : ℤ)⟧' =
      ProductCone.map P.product Q.product e.hom ≫ Q.connecting := sorry

/-- A presentation isomorphism commutes with every canonical stage projection. -/
@[reassoc, stacks 08TC]
theorem stageProjection_naturality
    {K L : SequentialInverseSystem D} {e : K ≅ L} {X Y : D}
    {P : Presentation K X} {Q : Presentation L Y}
    (Φ : Presentation.Iso e P Q) (n : ℕ) :
    P.stageProjection n ≫ e.hom.app (op n) =
      Φ.iso.hom ≫ Q.stageProjection n := sorry

end Presentation.Iso

end CategoryTheory.HomotopyLimit
