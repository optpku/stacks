/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Comparison

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.SmallToBig

/-- The inverse image of a small étale sheaf satisfies descent for the big fppf topology. -/
theorem inverseImage_isSheaf_fppf (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
      (((siteMorphismOfTopoi S)⁻¹).obj F).1 := sorry

/-- The fppf sheaf obtained by bundling the small-to-big inverse image. -/
noncomputable def inverseImageFppf (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  ⟨(((siteMorphismOfTopoi S)⁻¹).obj F).1, inverseImage_isSheaf_fppf S F⟩

/-- The standard fppf inverse image is canonically the bundled small-to-big inverse image. -/
noncomputable def toFppfInverseImageIso (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    ((StandardTopology.toFppf .etale S)⁻¹).obj
        (((siteMorphismOfTopoi S)⁻¹).obj F) ≅ inverseImageFppf S F :=
  -- Local instance justification (defeq pin): the continuous identity-site presentation
  -- must be fixed while constructing the canonical sheaf pullback comparison.
  let _ : Functor.IsContinuous (𝟭 (Over S))
      (StandardTopology.etale.overTopology S)
      (StandardTopology.fppf.overTopology S) :=
    (StandardTopology.toFppf_isMorphismOfSites (τ := .etale) S).toIsContinuous
  -- Local instance justification (defeq pin): the sheaf pullback construction requires
  -- the right-adjoint presentation associated to the same continuous identity functor.
  let _ :
      ((𝟭 (Over S)).sheafPushforwardContinuous (Type (u + 1))
        (StandardTopology.etale.overTopology S)
        (StandardTopology.fppf.overTopology S)).IsRightAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (𝟭 (Over S)) (Type (u + 1))
      (StandardTopology.etale.overTopology S)
      (StandardTopology.fppf.overTopology S)).isRightAdjoint
  (Functor.sheafPullbackConstruction.sheafPullbackIso
      (𝟭 (Over S)) (Type (u + 1))
      (StandardTopology.etale.overTopology S)
      (StandardTopology.fppf.overTopology S)).app
      (((siteMorphismOfTopoi S)⁻¹).obj F) ≪≫
    (presheafToSheaf (StandardTopology.fppf.overTopology S) (Type (u + 1))).mapIso
      ((((𝟭 (Over S)).op.lanAdjunction (Type (u + 1))).leftAdjointUniq
          Adjunction.id).app (((siteMorphismOfTopoi S)⁻¹).obj F).1) ≪≫
    (sheafificationIso (inverseImageFppf S F)).symm

end AlgebraicGeometry.Scheme.Etale.SmallToBig
