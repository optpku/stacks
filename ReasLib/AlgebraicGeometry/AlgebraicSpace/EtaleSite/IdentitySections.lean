/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSheafSpace

/-!
# Sections at identity objects of small étale sites
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

private theorem etaleRestriction_idHom_w (U : smallEtaleSite X) :
    ofOverMap (𝟙 U.left) ≫ U.hom =
      ((etaleRestriction U.hom).obj (smallEtaleSite.id U.left)).hom := sorry

/-- The identity-on-left comparison from the identity object of `U`, postcomposed along
`U.hom`, to `U` itself. -/
@[no_expose] def etaleRestriction_idHom (U : smallEtaleSite X) :
    (etaleRestriction U.hom).obj (smallEtaleSite.id U.left) ⟶ U :=
  MorphismProperty.CostructuredArrow.homMk (𝟙 U.left) trivial (etaleRestriction_idHom_w U)

/-- `etaleRestriction_idHom U` retains the identity on the underlying scheme over `S`. -/
theorem etaleRestriction_idHom_left (U : smallEtaleSite X) :
    (etaleRestriction_idHom U).left = 𝟙 U.left := by
  unfold etaleRestriction_idHom
  rfl

/-- Evaluation of `U.hom⁻¹ G` at the identity object of `U`, obtained from a section of `G`
over `U`. -/
def pushforwardSectionToInverseImageEval {U : smallEtaleSite X}
    (G : Sheaf (smallEtaleTopology X) (Type (u + 1))) (t : G.obj.obj (op U)) :
    etaleInverseImageSections U.hom G :=
  (smallEtaleMorphismOfTopoi_inverseImage_obj U.hom G
      (smallEtaleSite.id U.left)).inv
    (G.obj.map (op (etaleRestriction_idHom U)) t)

/-- Evaluation in the inverse-image sheaf is obtained by restricting the section along
the identity-on-domain chart morphism and applying the inverse-image identification. -/
theorem pushforwardSectionToInverseImageEval_eq {U : smallEtaleSite X}
    (G : Sheaf (smallEtaleTopology X) (Type (u + 1))) (t : G.obj.obj (op U)) :
    pushforwardSectionToInverseImageEval G t =
      (smallEtaleMorphismOfTopoi_inverseImage_obj U.hom G
          (smallEtaleSite.id U.left)).inv
        (G.obj.map (op (etaleRestriction_idHom U)) t) :=
  rfl

private theorem evalIdentityToSections_naturality {T : Over S}
    (G : Sheaf (smallEtaleTopology (ofOver T)) (Type (u + 1)))
    (s : G.obj.obj (op (smallEtaleSite.id T)))
    {U V : (smallEtaleSite (ofOver T))ᵒᵖ} (f : U ⟶ V) :
    G.obj.map f (G.obj.map (smallEtaleSite.homToId T U.unop).op s) =
      G.obj.map (smallEtaleSite.homToId T V.unop).op s := sorry

/-- Compatible sections of a small étale sheaf on `ofOver T` obtained by restricting an
identity-object value along `smallEtaleSite.homToId`. -/
@[no_expose] def evalIdentityToSections {T : Over S}
    (G : Sheaf (smallEtaleTopology (ofOver T)) (Type (u + 1)))
    (s : G.obj.obj (op (smallEtaleSite.id T))) :
    G.obj.sections :=
  ⟨fun U ↦ G.obj.map (smallEtaleSite.homToId T U.unop).op s, fun f ↦ evalIdentityToSections_naturality G s f⟩

/-- Values of `evalIdentityToSections` at an object `U` are restriction of the
identity-object section along `smallEtaleSite.homToId`. -/
theorem evalIdentityToSections_apply {T : Over S}
    (G : Sheaf (smallEtaleTopology (ofOver T)) (Type (u + 1)))
    (s : G.obj.obj (op (smallEtaleSite.id T))) (U : (smallEtaleSite (ofOver T))ᵒᵖ) :
    (evalIdentityToSections G s).val U =
      G.obj.map (smallEtaleSite.homToId T U.unop).op s := by
  unfold evalIdentityToSections
  rfl

end AlgebraicGeometry.AlgebraicSpace
