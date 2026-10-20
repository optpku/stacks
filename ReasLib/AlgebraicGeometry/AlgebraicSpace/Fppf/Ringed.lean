/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.CategoryTheory.Sites.Over.SheafCompose
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AtlasRinged
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sites.ModuleSheafification
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.Comparison

/-!
# Fppf ringed site and ringed comparisons `ε_X`, `a_X`

The structure sheaf on `(Spaces/X)_fppf` has the same underlying presheaf
`U ↦ Γ(U, 𝒪_U)` as the big étale structure sheaf. The identity functor of
`Over X` enhances `ε_X` to a morphism of ringed sites, and
`a_X = π_X ∘ ε_X` is the composite with `Etale.Atlas.etalePiRingedHom`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open AlgebraicGeometry.AlgebraicSpace.Fppf

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Fppf

variable {S : Scheme.{u}}

/-- The ring presheaf on `(Spaces/X)_fppf` with value `Γ(U, 𝒪_U)`, the same
underlying presheaf as on `(Spaces/X)_étale`. -/
abbrev overFppfStructurePresheaf (X : AlgebraicSpace S) :
    (Over X)ᵒᵖ ⥤ RingCat.{u} :=
  Etale.Atlas.overEtaleStructurePresheaf X

/-- The value of `overFppfStructurePresheaf X` at `U` is `Γ(U.left, 𝒪_{U.left})`. -/
theorem overFppfStructurePresheaf_obj (X : AlgebraicSpace S) (U : Over X) :
    (overFppfStructurePresheaf X).obj (op U) =
      (forget₂ CommRingCat RingCat).obj (globalSectionsRing U.left) :=
  rfl

/-- The global-sections presheaf on `(Spaces/X)_fppf` is a sheaf. -/
theorem overFppfStructurePresheaf_isSheaf (X : AlgebraicSpace S) :
    Presheaf.IsSheaf (overFppfTopology X) (overFppfStructurePresheaf X) :=
  sorry

/-- The structure sheaf `𝒪` on `(Spaces/X)_fppf`, with value `U ↦ Γ(U, 𝒪_U)`. -/
def overFppfStructureSheaf (X : AlgebraicSpace S) :
    Sheaf (overFppfTopology X) RingCat.{u} :=
  ⟨overFppfStructurePresheaf X, overFppfStructurePresheaf_isSheaf X⟩

/-- On an algebraic space `U` over `X`, the big fppf structure sheaf has value
`Γ(U, 𝒪_U)`. -/
theorem overFppfStructureSheaf_obj (X : AlgebraicSpace S) (U : Over X) :
    (overFppfStructureSheaf X).obj.obj (op U) =
      (forget₂ CommRingCat RingCat).obj (globalSectionsRing U.left) :=
  rfl

/-- The big fppf ringed site `((Spaces/X)_fppf, 𝒪)`. -/
abbrev overFppfRingedSite (X : AlgebraicSpace S) : RingedSite.{u + 1, u + 1, u} :=
  RingedSite.ofRingSheaf (overFppfTopology X) (overFppfStructureSheaf X)

/-- The structure sheaf of `overFppfRingedSite X` is `overFppfStructureSheaf X`. -/
theorem overFppfRingedSite_structureSheaf (X : AlgebraicSpace S) :
    (overFppfRingedSite X).structureSheaf = overFppfStructureSheaf X :=
  rfl

/-- The identity coefficient comparison commutes with restriction. -/
theorem epsilonRingedHom_naturality (X : AlgebraicSpace S)
    {U V : (Over X)ᵒᵖ} (g : U ⟶ V) :
    (Etale.Atlas.overEtaleStructureSheaf X).obj.map g ≫ 𝟙 _ =
      𝟙 _ ≫
        (((𝟭 (Over X)).sheafPushforwardContinuous RingCat.{u}
          (overEtaleTopology X) (overFppfTopology X)).obj
            (overFppfStructureSheaf X)).obj.map g :=
  sorry

/-- The morphism of ringed sites `ε_X : ((Spaces/X)_fppf, 𝒪) ⟶ ((Spaces/X)_étale, 𝒪)`,
with identity base functor and identity comparison of the common structure
presheaf. -/
def epsilonRingedHom (X : AlgebraicSpace S) :
    RingedSite.Hom (overFppfRingedSite X) (Etale.Atlas.overEtaleRingedSite X) where
  base := 𝟭 (Over X)
  isMorphismOfSites := epsilon_isMorphismOfSites X
  structureSheafMap :=
    ObjectProperty.homMk
      { app := fun _ ↦ 𝟙 _
        naturality := fun _ _ g ↦ epsilonRingedHom_naturality X g }

/-- The base functor of `epsilonRingedHom X` is the identity of `Over X`. -/
theorem epsilonRingedHom_base (X : AlgebraicSpace S) :
    (epsilonRingedHom X).base = 𝟭 (Over X) :=
  rfl

/-- The structure-sheaf map of `epsilonRingedHom X` is the identity comparison of
the common global-sections presheaf. -/
theorem epsilonRingedHom_structureSheafMap_app (X : AlgebraicSpace S)
    (U : (Over X)ᵒᵖ) :
    (epsilonRingedHom X).structureSheafMap.hom.app U = 𝟙 _ :=
  rfl

/-- The morphism of ringed sites `a_X = π_X ∘ ε_X` from
`((Spaces/X)_fppf, 𝒪)` to `(X_étale, 𝒪_X)`. -/
def aRingedHom (X : AlgebraicSpace S) :
    RingedSite.Hom (overFppfRingedSite X) (ringedSite X) :=
  RingedSite.Hom.comp (epsilonRingedHom X) (Etale.Atlas.etalePiRingedHom X)

/-- `aRingedHom X` is the composite of `epsilonRingedHom X` with
`Etale.Atlas.etalePiRingedHom X`. -/
theorem aRingedHom_eq_comp (X : AlgebraicSpace S) :
    aRingedHom X = RingedSite.Hom.comp (epsilonRingedHom X) (Etale.Atlas.etalePiRingedHom X) :=
  rfl

/-- The base functor of `aRingedHom X` is étale relocalization along `𝟙 X`. -/
theorem aRingedHom_base (X : AlgebraicSpace S) :
    (aRingedHom X).base = relocalizationFunctor (𝟙 X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Fppf

end

end
