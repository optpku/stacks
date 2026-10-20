/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.GradedSections
import StacksCheckRecall

@[expose] public section

open scoped AlgebraicGeometry DirectSum

universe u v

namespace AlgebraicGeometry

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable (Mpiece : ℤ → Type u) [∀ n : ℤ, AddCommGroup (Mpiece n)]
variable (P : Proj.AssociatedModule.Presentation 𝒜 Mpiece)
variable [DirectSum.Gmodule (fun d : ℕ ↦ 𝒜 d) Mpiece]
variable [DirectSum.Gmodule (fun d : ℕ ↦ 𝒜 d)
  (fun n : ℤ ↦ Γ(P.associatedTwist n, ⊤))]
variable (hP : P.IsGraded)

/-- An ambient choice of the associated sheaves of all integral shifts of a graded module. -/
class HasProjAssociatedTwistPresentation where
  /-- The chosen family `~(M(n))` and its degreewise maps to global sections. -/
  presentation : Proj.AssociatedModule.Presentation 𝒜 Mpiece

/-- The associated sheaf `~(M(n))` supplied by the ambient presentation. -/
abbrev projAssociatedTwist
    [hP : HasProjAssociatedTwistPresentation 𝒜 Mpiece] (n : ℤ) :
    (Proj 𝒜).Modules :=
  hP.presentation.associatedTwist n

/-- A degree-zero associated sheaf together with its canonical map to global sections. -/
structure ProjAssociatedModuleSheaf where
  /-- The sheaf `~M`. -/
  sheaf : (Proj 𝒜).Modules
  /-- The degree-zero map `M₀ ⟶ Γ(Proj(S), ~M)`. -/
  sectionMap : Mpiece 0 →+ Γ(sheaf, ⊤)

/-- The degree-zero member of the ambient associated-twist presentation. -/
abbrev projAssociatedModuleSheaf
    [hP : HasProjAssociatedTwistPresentation 𝒜 Mpiece] :
    ProjAssociatedModuleSheaf 𝒜 Mpiece where
  sheaf := projAssociatedTwist 𝒜 Mpiece 0
  sectionMap := hP.presentation.sectionMap 0

variable {𝒜}

/-- The degreewise section maps of an associated-twist presentation assemble to a linear map
from the graded module to the direct sum of the global sections of its twists. -/
noncomputable abbrev gradedModuleToProjAssociatedTwistGlobalSectionsMap
    (Mpiece : ℤ → Type u) [∀ n : ℤ, AddCommGroup (Mpiece n)]
    (P : Proj.AssociatedModule.Presentation 𝒜 Mpiece)
    [DirectSum.Gmodule (fun d : ℕ ↦ 𝒜 d) Mpiece]
    [DirectSum.Gmodule (fun d : ℕ ↦ 𝒜 d)
      (fun n : ℤ ↦ Γ(P.associatedTwist n, ⊤))]
    (hP : P.IsGraded) :
    (⨁ n : ℤ, Mpiece n) →ₗ[(⨁ d : ℕ, 𝒜 d)]
      (⨁ n : ℤ, Γ(P.associatedTwist n, ⊤)) :=
  Proj.AssociatedModule.Presentation.gradedMap Mpiece P hP

#check
  (AlgebraicGeometry.Proj.AssociatedModule.Presentation 𝒜 Mpiece : Type (u + 1))

#check
  (AlgebraicGeometry.Proj.AssociatedModule.Presentation.ofFamily
      P.associatedTwist P.sectionMap :
    AlgebraicGeometry.Proj.AssociatedModule.Presentation 𝒜 Mpiece)

#check
  (AlgebraicGeometry.Proj.AssociatedModule.Presentation.IsGraded P : Prop)

#check
  (AlgebraicGeometry.Proj.AssociatedModule.Presentation.gradedMap Mpiece P hP :
    (⨁ n : ℤ, Mpiece n) →ₗ[(⨁ d : ℕ, 𝒜 d)]
      (⨁ n : ℤ, Γ(P.associatedTwist n, ⊤)))

#check
  (AlgebraicGeometry.Proj.AssociatedModule.Presentation.gradedMap_of Mpiece P hP :
    ∀ (n : ℤ) (m : Mpiece n),
      AlgebraicGeometry.Proj.AssociatedModule.Presentation.gradedMap Mpiece P hP
          (DirectSum.of Mpiece n m) =
        DirectSum.of (fun i : ℤ ↦ Γ(P.associatedTwist i, ⊤)) n
          (P.sectionMap n m))

/- 27.10.1.6: The canonical graded-module map
`M ⟶ ⨁ n : ℤ, Γ(X, ~(M(n)))`. -/
@[stacks 01MR] #check
  (AlgebraicGeometry.gradedModuleToProjAssociatedTwistGlobalSectionsMap
      Mpiece P hP :
    (⨁ n : ℤ, Mpiece n) →ₗ[(⨁ d : ℕ, 𝒜 d)]
      (⨁ n : ℤ, Γ(P.associatedTwist n, ⊤)))

end AlgebraicGeometry
