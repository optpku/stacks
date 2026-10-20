/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pushforward

/-!
# Quasi-coherent modules and open immersions
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {A : Type u} [CommRing A]
variable {U X : Scheme.{u}}

/-- Restricting the affine reconstruction morphism for the pushforward of a module along an
open immersion, followed by the restriction-pushforward counit. -/
noncomputable def tildeGlobalSectionsRestrictMap
    (j : U ⟶ Spec (.of A)) [IsOpenImmersion j]
    (ℱ : U.Modules) :
    (tilde ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj ((pushforward j).obj ℱ))).restrict j ⟶
      ℱ :=
  (restrictFunctor j).map
      (fromTildeΓ (R := CommRingCat.of A) (M := (pushforward j).obj ℱ)) ≫
    (restrictAdjunction j).counit.app ℱ

/-- For a quasi-compact open immersion into an affine scheme, the restricted affine
reconstruction morphism of a quasi-coherent module is an isomorphism. -/
instance isIso_tildeGlobalSectionsRestrictMap
    (j : U ⟶ Spec (.of A)) [IsOpenImmersion j] [QuasiCompact j]
    (ℱ : U.Modules) [ℱ.IsQuasicoherent] :
    IsIso (tildeGlobalSectionsRestrictMap j ℱ) := sorry

/-- Every quasi-coherent module on the domain of a quasi-compact open immersion extends to a
quasi-coherent module on its codomain. -/
theorem exists_quasiCoherentExtension
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (G : U.Modules) [G.IsQuasicoherent] :
    ∃ H : X.Modules, H.IsQuasicoherent ∧ Nonempty (H.restrict j ≅ G) := by
  exact ⟨(pushforward j).obj G, inferInstance, ⟨(asIso (restrictAdjunction j).counit).app G⟩⟩

/-- A quasi-coherent subobject of the restriction of a quasi-coherent module along a
quasi-compact open immersion extends compatibly to a quasi-coherent subobject. -/
theorem exists_quasiCoherentSubsheafExtension
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (F : X.Modules) [F.IsQuasicoherent]
    (G : Subobject (F.restrict j)) [(G : U.Modules).IsQuasicoherent] :
    ∃ H : Subobject F,
      (H : X.Modules).IsQuasicoherent ∧
        ∃ e : (H : X.Modules).restrict j ≅ (G : U.Modules),
          e.hom ≫ G.arrow = (restrictFunctor j).map H.arrow := sorry

/-- On a quasi-compact quasi-separated scheme, a finite-type quasi-coherent subobject over a
quasi-compact open subscheme extends compatibly to a finite-type quasi-coherent subobject. -/
theorem exists_finiteTypeQuasiCoherentSubsheafExtension
    [CompactSpace X] [QuasiSeparatedSpace X]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (F : X.Modules) [F.IsQuasicoherent]
    (G : Subobject (F.restrict j))
    [(G : U.Modules).IsQuasicoherent] [(G : U.Modules).IsFiniteType] :
    ∃ H : Subobject F,
      (H : X.Modules).IsQuasicoherent ∧ (H : X.Modules).IsFiniteType ∧
        ∃ e : (H : X.Modules).restrict j ≅ (G : U.Modules),
          e.hom ≫ G.arrow = (restrictFunctor j).map H.arrow := sorry

/-- Every finite-type quasi-coherent module on a quasi-compact open subscheme of a
quasi-compact quasi-separated scheme extends to a finite-type quasi-coherent module. -/
theorem exists_finiteTypeQuasiCoherentExtension
    [CompactSpace X] [QuasiSeparatedSpace X]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (G : U.Modules) [G.IsQuasicoherent] [G.IsFiniteType] :
    ∃ G' : X.Modules,
      G'.IsQuasicoherent ∧ G'.IsFiniteType ∧ Nonempty (G'.restrict j ≅ G) := sorry

/-- A morphism from a quasi-coherent module into the restriction of a quasi-coherent module
along a quasi-compact open immersion extends compatibly from a quasi-coherent module. -/
theorem exists_quasiCoherentMorphismExtension
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (F : X.Modules) [F.IsQuasicoherent]
    (G : U.Modules) [G.IsQuasicoherent] (φ : G ⟶ F.restrict j) :
    ∃ H : X.Modules,
      H.IsQuasicoherent ∧
        ∃ ψ : H ⟶ F, ∃ e : H.restrict j ≅ G,
          e.hom ≫ φ = (restrictFunctor j).map ψ := sorry

end AlgebraicGeometry.Scheme.Modules
