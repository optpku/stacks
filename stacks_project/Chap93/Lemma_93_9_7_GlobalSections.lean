/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Affine

/-!
# Global sections of affine scheme deformations
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace FlatSchemeCat

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The algebra on global functions induced by the stored structure morphism. -/
abbrev algebraOfStructureHom (Y : FlatSchemeCat Λ k) :
    Algebra Y.base.carrier Γ(Y.scheme, ⊤) :=
  Scheme.Hom.globalSectionsAlgebra Y.structureHom

/-- The algebra map on global functions is pullback along the structure morphism
following the canonical identification with global functions on the affine base. -/
theorem algebraOfStructureHom_algebraMap (Y : FlatSchemeCat Λ k) :
    (algebraOfStructureHom Y).algebraMap =
      ((Scheme.ΓSpecIso (CommRingCat.of Y.base.carrier)).inv ≫ Y.structureHom.appTop).hom :=
  Scheme.Hom.globalSectionsMap_eq_appTop Y.structureHom

variable (Λ k) (P : Type u) [CommRing P] [Algebra k P]

#check (FlatSchemeCat.globalSectionsBasedFunctor Λ k P :
  BasedCategory.ofFunctor (FlatSchemeCat.schemeDeformationForget Λ k P) ⥤ᵇ
    BasedCategory.ofFunctor (FlatSchemeCat.algebraDeformationForget Λ k P))

end FlatSchemeCat
