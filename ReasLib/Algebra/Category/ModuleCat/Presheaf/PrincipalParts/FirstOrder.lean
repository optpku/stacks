/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.PrincipalParts
public import ReasLib.Algebra.Module.PrincipalParts.RingHom.FirstOrder

/-!
# The first principal-parts sequence for module presheaves

This file constructs the first principal-parts sequence for a morphism of commutative-ring
presheaves.  It is independent of a Grothendieck topology: the sheaf-level sequence is obtained
by applying module sheafification to this owner.
-/

@[expose] public section

open CategoryTheory
open PresheafOfModules.DifferentialsConstruction

noncomputable section

universe u v

namespace PresheafOfModules.PrincipalParts.FirstOrder

variable {C : Type u} [Category.{v} C]
variable {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{max u v}}

/-- The cotangent tensor presheaf `Ω[O₂/O₁] ⊗[O₂] F`. -/
noncomputable abbrev cotangent (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) :
    PresheafOfModules (ringPresheaf O₂) :=
  PresheafOfModules.Monoidal.tensorObj (relativeDifferentials' phi) F

/-- The component of the canonical cotangent arrow into first principal parts. -/
noncomputable def cotangentToApp (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (X : Cᵒᵖ) :
    (cotangent phi F).obj X ⟶ (PrincipalParts.presheaf phi F 1).obj X :=
  _root_.PrincipalParts.RingHom.FirstOrder.cotangentTo (phi.app X).hom (F.obj X)

/-- The cotangent components commute with restriction maps. -/
theorem cotangentToApp_naturality (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (cotangent phi F).map f ≫
        (ModuleCat.restrictScalars (((ringPresheaf O₂).map f).hom)).map
          (cotangentToApp phi F Y) =
      cotangentToApp phi F X ≫ (PrincipalParts.presheaf phi F 1).map f := sorry

/-- The canonical cotangent arrow into the first principal-parts presheaf. -/
noncomputable def cotangentTo (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) :
    cotangent phi F ⟶ PrincipalParts.presheaf phi F 1 where
  app X := cotangentToApp phi F X
  naturality := cotangentToApp_naturality phi F

/-- The component of the canonical first-principal-parts projection. -/
noncomputable def projectionApp (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) (X : Cᵒᵖ) :
    (PrincipalParts.presheaf phi F 1).obj X ⟶ F.obj X :=
  _root_.PrincipalParts.RingHom.FirstOrder.projection (phi.app X).hom (F.obj X)

/-- The projection components commute with restriction maps. -/
theorem projectionApp_naturality (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (PrincipalParts.presheaf phi F 1).map f ≫
        (ModuleCat.restrictScalars (((ringPresheaf O₂).map f).hom)).map
          (projectionApp phi F Y) =
      projectionApp phi F X ≫ F.map f := sorry

/-- The canonical projection from first principal parts to the original module presheaf. -/
noncomputable def projection (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) :
    PrincipalParts.presheaf phi F 1 ⟶ F where
  app X := projectionApp phi F X
  naturality := projectionApp_naturality phi F

/-- The cotangent arrow followed by the first-principal-parts projection is zero. -/
theorem zero (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) :
    cotangentTo phi F ≫ projection phi F = 0 := sorry

/-- The first principal-parts short complex of a module presheaf. -/
@[stacks 09CN "presheaf first principal-parts sequence"]
noncomputable def sequence (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) :
    ShortComplex (PresheafOfModules (ringPresheaf O₂)) :=
  ShortComplex.mk (cotangentTo phi F) (projection phi F) (zero phi F)

section Functoriality

variable {F G H : PresheafOfModules (ringPresheaf O₂)}

/-- The morphism on cotangent tensor presheaves induced by a module-presheaf morphism. -/
noncomputable abbrev cotangentMap (phi : O₁ ⟶ O₂) (alpha : F ⟶ G) :
    cotangent phi F ⟶ cotangent phi G :=
  PresheafOfModules.Monoidal.tensorHom (𝟙 (relativeDifferentials' phi)) alpha

/-- Cotangent tensor functoriality preserves identity morphisms. -/
@[simp]
theorem cotangentMap_id (phi : O₁ ⟶ O₂) :
    cotangentMap phi (𝟙 F) = 𝟙 (cotangent phi F) := sorry

/-- Cotangent tensor functoriality preserves composition. -/
@[simp]
theorem cotangentMap_comp (phi : O₁ ⟶ O₂) (alpha : F ⟶ G) (beta : G ⟶ H) :
    cotangentMap phi (alpha ≫ beta) =
      cotangentMap phi alpha ≫ cotangentMap phi beta := sorry

/-- Tensoring with the relative-differentials presheaf defines an endofunctor on module
presheaves. -/
noncomputable def cotangentFunctor (phi : O₁ ⟶ O₂) :
    PresheafOfModules (ringPresheaf O₂) ⥤ PresheafOfModules (ringPresheaf O₂) where
  obj F := cotangent phi F
  map alpha := cotangentMap phi alpha
  map_id _ := cotangentMap_id phi
  map_comp alpha beta := cotangentMap_comp phi alpha beta

/-- Naturality of the cotangent arrow in the module-presheaf argument. -/
theorem cotangentTo_naturality (phi : O₁ ⟶ O₂) (alpha : F ⟶ G) :
    cotangentMap phi alpha ≫ cotangentTo phi G =
      cotangentTo phi F ≫ PrincipalParts.map phi F 1 alpha := sorry

/-- Naturality of the first-principal-parts projection in the module-presheaf argument. -/
theorem projection_naturality (phi : O₁ ⟶ O₂) (alpha : F ⟶ G) :
    PrincipalParts.map phi F 1 alpha ≫ projection phi G =
      projection phi F ≫ alpha := sorry

/-- The cotangent arrows form a natural transformation into first principal parts. -/
noncomputable def cotangentToNatTrans (phi : O₁ ⟶ O₂) :
    cotangentFunctor phi ⟶ PrincipalParts.functor phi 1 where
  app F := cotangentTo phi F
  naturality _ _ alpha := cotangentTo_naturality phi alpha

/-- The first-principal-parts projections form a natural transformation to the identity
functor. -/
noncomputable def projectionNatTrans (phi : O₁ ⟶ O₂) :
    PrincipalParts.functor phi 1 ⟶ 𝟭 (PresheafOfModules (ringPresheaf O₂)) where
  app F := projection phi F
  naturality _ _ alpha := projection_naturality phi alpha

/-- The morphism of first-principal-parts short complexes induced by a module-presheaf
morphism. -/
noncomputable def sequenceMap (phi : O₁ ⟶ O₂) (alpha : F ⟶ G) :
    sequence phi F ⟶ sequence phi G :=
  ShortComplex.Hom.mk (cotangentMap phi alpha) (PrincipalParts.map phi F 1 alpha) alpha
    (cotangentTo_naturality phi alpha) (projection_naturality phi alpha)

/-- The first-principal-parts sequence map preserves identity morphisms. -/
@[simp]
theorem sequenceMap_id (phi : O₁ ⟶ O₂) :
    sequenceMap phi (𝟙 F) = 𝟙 (sequence phi F) := sorry

/-- The first-principal-parts sequence map preserves composition. -/
@[simp]
theorem sequenceMap_comp (phi : O₁ ⟶ O₂) (alpha : F ⟶ G) (beta : G ⟶ H) :
    sequenceMap phi (alpha ≫ beta) = sequenceMap phi alpha ≫ sequenceMap phi beta := sorry

/-- The first-principal-parts short complex is functorial in the module presheaf. -/
noncomputable def sequenceFunctor (phi : O₁ ⟶ O₂) :
    PresheafOfModules (ringPresheaf O₂) ⥤
      ShortComplex (PresheafOfModules (ringPresheaf O₂)) where
  obj F := sequence phi F
  map alpha := sequenceMap phi alpha
  map_id _ := sequenceMap_id phi
  map_comp alpha beta := sequenceMap_comp phi alpha beta

end Functoriality

/-- The first principal-parts sequence of module presheaves is short exact. -/
@[stacks 09CN "presheaf first-order short exactness"]
theorem shortExact (phi : O₁ ⟶ O₂)
    (F : PresheafOfModules (ringPresheaf O₂)) :
    (sequence phi F).ShortExact := sorry

end PresheafOfModules.PrincipalParts.FirstOrder
