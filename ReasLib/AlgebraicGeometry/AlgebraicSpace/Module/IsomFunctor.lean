/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HomFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sites.Fpqc

/-!
# The Isom functor of quasi-coherent modules on an algebraic space

The invertible module maps form a subfunctor of the Hom presheaf on schemes
over the base algebraic space. This presheaf satisfies fpqc descent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Restriction of an invertible `𝒪_{X_T}`-module map along a morphism of
schemes over `B` remains invertible. -/
theorem baseChangeHom_isIso (f : X ⟶ B) (F G : X.Modules) {σ τ : SchemeOver B}
    (h : τ ⟶ σ) {u : baseChangeModule f σ.hom F ⟶ baseChangeModule f σ.hom G}
    (hu : IsIso u) : IsIso (baseChangeHom f F G h u) :=
  sorry

/-- The subfunctor of `Hom(F, G)` whose value on a scheme `T` over `B` is the
set of invertible `𝒪_{X_T}`-module maps `F_T ⟶ G_T`. -/
def isomSubfunctor (f : X ⟶ B) (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] : Subfunctor (homFunctor f F G) where
  obj σ := {u | IsIso u}
  map h u hu := baseChangeHom_isIso f F G h.unop hu

/-- The presheaf on schemes over `B` whose sections are invertible maps
between the base changes of `F` and `G`. -/
def isomFunctor (f : X ⟶ B) (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1) :=
  (isomSubfunctor f F G).toFunctor

/-- An invertible Hom-section determines a section of the Isom presheaf. -/
def IsomFunctor.mk (f : X ⟶ B) (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    {σ : SchemeOver B} (u : (homFunctor f F G).obj (op σ)) [IsIso u] :
    (isomFunctor f F G).obj (op σ) :=
  ⟨u, ‹IsIso u›⟩

/-- Membership in the Isom subfunctor is invertibility of the corresponding
Hom-section. -/
theorem mem_isomSubfunctor (f : X ⟶ B) (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] {σ : SchemeOver B}
    (u : (homFunctor f F G).obj (op σ)) :
    u ∈ (isomSubfunctor f F G).obj (op σ) ↔ IsIso u :=
  Iff.rfl

/-- The presheaf of isomorphisms between two quasi-coherent modules on an
algebraic space satisfies the sheaf property for the fpqc topology. -/
theorem isomFunctor_isSheaf_fpqc {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    Presheaf.IsSheaf (SchemeOver.fpqcTopology B) (isomFunctor f F G) :=
  sorry

/-- Compatible families of isomorphisms `F_{T_i} ⟶ G_{T_i}` on an fpqc covering of
schemes over `B` glue uniquely to an isomorphism `F_T ⟶ G_T`. -/
theorem isomFunctor_isSheafFor_fpqcCovering {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    {ι : Type u} {U : SchemeOver B} {V : ι → SchemeOver B} (h : ∀ i, V i ⟶ U)
    (h_cover : Presieve.ofArrows V h ∈ SchemeOver.fpqcPrecoverage B U) :
    Presieve.IsSheafFor (isomFunctor f F G) (Presieve.ofArrows V h) :=
  sorry

/-- An `𝒪_{X_T}`-module map whose restrictions along an fpqc covering of schemes
over `B` are isomorphisms is itself an isomorphism. -/
theorem isIso_of_fpqcCovering {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    {ι : Type u} {U : SchemeOver B} {V : ι → SchemeOver B} (h : ∀ i, V i ⟶ U)
    (h_cover : Presieve.ofArrows V h ∈ SchemeOver.fpqcPrecoverage B U)
    (u : baseChangeModule f U.hom F ⟶ baseChangeModule f U.hom G)
    (h_iso : ∀ i, IsIso (baseChangeHom f F G (h i) u)) : IsIso u :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
