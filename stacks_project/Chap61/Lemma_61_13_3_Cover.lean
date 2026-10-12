/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import ReasLib.CategoryTheory.Sites.Family.Covering
public import ReasLib.CategoryTheory.Sites.EnoughObjects
public import ReasLib.CategoryTheory.Sites.WeaklyContractible
public import stacks_project.Chap61.Definition_61_12_8_Presentation
public import stacks_project.Chap61.Definition_61_11_1_WContractible
public import stacks_project.Chap61.Lemma_61_13_2_Characterization

/-!
# Affine w-contractible covers in the pro-étale topology

Every scheme admits a pro-étale cover by affine spectra of w-contractible
rings, and every object of a chosen big pro-étale site admits such a covering
family.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme.Proetale

/-- Every scheme admits a pro-étale cover whose members are affine with
w-contractible rings of global sections. -/
theorem exists_affine_wContractibleRing_cover (T : Scheme.{u}) :
    ∃ 𝒰 : T.Cover Scheme.proetalePrecoverage,
      ∀ i, IsAffine (𝒰.X i) ∧ IsWContractibleRing Γ(𝒰.X i, ⊤) := sorry

/-- Every scheme admits a jointly surjective weakly étale family of maps from
spectra of w-contractible rings which covers in the pro-étale precoverage. -/
theorem exists_affineCover_isWContractibleRing (T : Scheme.{u}) :
    ∃ 𝒰 : T.AffineCover (@WeaklyEtale),
      Presieve.ofArrows (fun j ↦ Spec (𝒰.X j)) 𝒰.f ∈ Scheme.proetalePrecoverage T ∧
        ∀ j, IsWContractibleRing (𝒰.X j) := sorry

end AlgebraicGeometry.Scheme.Proetale

namespace AlgebraicGeometry.ChosenBigProetaleSite

/-- Every object of a chosen big pro-étale site admits a covering family whose
sources are affine and spectra of w-contractible rings. -/
@[stacks 098I]
theorem exists_affine_wContractibleRing_cover
    (X : ChosenBigProetaleSite.{u, v}) (T : X.carrier) :
    ∃ 𝒰 : SemiRepresentableFamily.Over.{u} T,
      𝒰.toPresieve ∈ X.pretopology T ∧
        ∀ i, IsAffine (X.toScheme.obj (𝒰.obj i).left) ∧
          IsWContractibleRing Γ(X.toScheme.obj (𝒰.obj i).left, ⊤) := sorry

/-- Every object of a chosen big pro-étale site admits a covering family whose
sources are affine and weakly contractible. -/
theorem exists_affine_weaklyContractible_cover
    (X : ChosenBigProetaleSite.{u, v}) (T : X.carrier) :
    ∃ 𝒰 : SemiRepresentableFamily.Over.{u} T,
      𝒰.toPresieve ∈ X.pretopology T ∧
        ∀ i, IsAffine (X.toScheme.obj (𝒰.obj i).left) ∧
          X.toGrothendieck.IsWeaklyContractible (𝒰.obj i).left := sorry

/-- The chosen big pro-étale topology has enough affine objects whose global
sections are w-contractible rings. -/
theorem hasEnough_isAffine_isWContractibleRing
    (X : ChosenBigProetaleSite.{u, v}) :
    X.toGrothendieck.HasEnoughObjectsWithProperty
      (fun T ↦ IsAffine (X.toScheme.obj T) ∧
        IsWContractibleRing Γ(X.toScheme.obj T, ⊤)) := sorry

end AlgebraicGeometry.ChosenBigProetaleSite
