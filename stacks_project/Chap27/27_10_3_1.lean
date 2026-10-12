/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.GradedSections
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry DirectSum

universe u v

section

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]
variable {Mpiece : ℤ → Type u} [∀ n : ℤ, AddCommGroup (Mpiece n)]
variable (P : AlgebraicGeometry.Proj.AssociatedModule.Presentation 𝒜 Mpiece)
variable [DirectSum.Gmodule (fun d : ℕ ↦ 𝒜 d) Mpiece]
variable [DirectSum.Gmodule (fun d : ℕ ↦ 𝒜 d)
  (fun n : ℤ ↦ Γ(P.associatedTwist n, ⊤))]
variable (hP : P.IsGraded)
variable (twistedAssociatedSheaf : ℤ → (AlgebraicGeometry.Proj 𝒜).Modules)
variable (comparisonIso : ∀ n : ℤ, twistedAssociatedSheaf n ≅ P.associatedTwist n)
variable (n : ℤ)

#check
  (AlgebraicGeometry.Proj.AssociatedModule.Presentation 𝒜 Mpiece : Type (u + 1))

#check
  (AlgebraicGeometry.Proj.AssociatedModule.Presentation.ofFamily
      P.associatedTwist P.sectionMap :
    AlgebraicGeometry.Proj.AssociatedModule.Presentation 𝒜 Mpiece)

#check
  (AlgebraicGeometry.Proj.AssociatedModule.Presentation.sectionMap P :
    ∀ n : ℤ, Mpiece n →+ Γ(P.associatedTwist n, ⊤))

#check
  (AlgebraicGeometry.Proj.AssociatedModule.Presentation.IsGraded P : Prop)

#check
  (AlgebraicGeometry.Proj.AssociatedModule.Presentation.sectionMapOfIso_apply
      P (comparisonIso n) :
    ∀ m : Mpiece n,
      AlgebraicGeometry.Proj.AssociatedModule.Presentation.sectionMapOfIso
          P (comparisonIso n) m =
        (AlgebraicGeometry.Scheme.Modules.globalSectionsMap (comparisonIso n).inv).hom
          (P.sectionMap n m))

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

/- 27.10.3.1: under the degree-one standard-open cover, the comparison
`twistedAssociatedSheaf n ≅ P.associatedTwist n` transports the degree-`n` section map to the
global sections of the twist `twistedAssociatedSheaf n`. -/
@[stacks 0AG3] #check
  (AlgebraicGeometry.Proj.AssociatedModule.Presentation.sectionMapOfIso P (comparisonIso n) :
    Mpiece n →+ Γ(twistedAssociatedSheaf n, ⊤))

end
