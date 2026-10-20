/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IsomFunctor

/-!
# The Isom functor of quasi-coherent modules on an algebraic space

The canonical invertibility subfunctor, its associated presheaf, and the
constructor of sections are available through this source-facing entry.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

#check (AlgebraicGeometry.AlgebraicSpace.Modules.isomSubfunctor :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
      (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent],
      Subfunctor (homFunctor f F G))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.isomFunctor :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
      (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent],
      (SchemeOver B)ᵒᵖ ⥤ Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.IsomFunctor.mk :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
      (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
      {σ : SchemeOver B} (u : (homFunctor f F G).obj (op σ)) [IsIso u],
      (isomFunctor f F G).obj (op σ))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.mem_isomSubfunctor :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
      (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
      {σ : SchemeOver B} (u : (homFunctor f F G).obj (op σ)),
      u ∈ (isomSubfunctor f F G).obj (op σ) ↔ IsIso u)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.baseChangeHom_isIso :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
      (f : X ⟶ B) (F G : X.Modules) {σ τ : SchemeOver B}
      (h : τ ⟶ σ) {u : baseChangeModule f σ.hom F ⟶ baseChangeModule f σ.hom G}
      (hu : IsIso u), IsIso (baseChangeHom f F G h u))

end AlgebraicGeometry.AlgebraicSpace.Modules
