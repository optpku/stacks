module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import stacks_project.Chap99.«99_3_1_1»

/-!
# The Isom functor of quasi-coherent modules on an algebraic space

This module constructs the subfunctor of `Hom(F, G)` on schemes over `B`
whose sections are the invertible `𝒪_{X_T}`-module maps `F_T ⟶ G_T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

namespace IsomFunctor

/-- The subfunctor of `Hom(F, G)` whose value on a scheme `T` over `B` is the
set of invertible `𝒪_{X_T}`-module maps `F_T ⟶ G_T`. -/
def subfunctor (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    Subfunctor (homFunctor f F G) where
  obj σ := {u | IsIso u}
  map := sorry

/-- The Type-valued functor `Isom(F, G)` associated to the invertibility
subfunctor of `Hom(F, G)`. -/
def functor (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (SchemeOver B)ᵒᵖ ⥤ Type (u + 1) :=
  (subfunctor f F G).toFunctor

/-- Membership in the Isom subfunctor is invertibility of the corresponding
Hom-section. -/
theorem mem_subfunctor (f : X ⟶ B) (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] {σ : SchemeOver B}
    (u : (homFunctor f F G).obj (op σ)) :
    u ∈ (subfunctor f F G).obj (op σ) ↔ IsIso u :=
  sorry

/-- Package an already invertible Hom-section as a section of `Isom(F, G)`. -/
def mk (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    {σ : SchemeOver B} (u : (homFunctor f F G).obj (op σ)) [IsIso u] :
    (functor f F G).obj (op σ) :=
  ⟨u, ‹IsIso u›⟩

end IsomFunctor

/-- The subfunctor of `Hom(F, G)` cut out by invertibility of `𝒪_{X_T}`-module
maps. -/
abbrev isomSubfunctor (f : X ⟶ B) (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] :=
  IsomFunctor.subfunctor f F G

/-- The functor `Isom(F, G) : (Sch/B)ᵒᵖ ⥤ Sets` sending a scheme `T` over `B`
to the type of `𝒪_{X_T}`-module isomorphisms `F_T ⟶ G_T`. -/
abbrev isomFunctor (f : X ⟶ B) (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] :=
  IsomFunctor.functor f F G

/-- Membership in `Isom(F, G)` is invertibility of the corresponding Hom-section. -/
theorem mem_isomSubfunctor (f : X ⟶ B) (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] {σ : SchemeOver B}
    (u : (homFunctor f F G).obj (op σ)) :
    u ∈ (isomSubfunctor f F G).obj (op σ) ↔ IsIso u :=
  sorry

/-- Restriction of an invertible `𝒪_{X_T}`-module map along a morphism of
schemes over `B` remains invertible. -/
theorem baseChangeHom_isIso (f : X ⟶ B) (F G : X.Modules) {σ τ : SchemeOver B}
    (h : τ ⟶ σ) {u : baseChangeModule f σ.hom F ⟶ baseChangeModule f σ.hom G}
    (hu : IsIso u) : IsIso (baseChangeHom f F G h u) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

