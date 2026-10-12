/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.Acyclicity
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 30.2.6: if `X` admits an open covering whose every finite intersection is affine open,
then for any quasi-coherent `𝒪_X`-module `ℱ` and any degree `p`, the
Čech cohomology of that cover on `X` identifies with the sheaf cohomology of `ℱ` as a
module over `Γ(X, 𝒪_X)`. -/
@[stacks 01XD] #check (
  AlgebraicGeometry.Scheme.moduleCechCohomology_isomorphic_cohomology_of_affineIntersections :
    ∀ {X : Scheme.{u}}
      {ι : Type u} (𝒰 : ι → X.Opens) (h𝒰 : TopologicalSpace.IsOpenCover 𝒰)
      (hAffine : ∀ n : ℕ, ∀ σ : Fin (n + 1) → ι, IsAffineOpen (⨅ a, 𝒰 (σ a)))
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] (p : ℕ),
      IsIsomorphic
        (ModuleCech.cohomology (⊤ : X.Opens)
          (Opens.Cover.overFamily (⊤ : X.Opens) 𝒰 h𝒰.iSup_eq_top) ℱ p)
        (Modules.cohomology ℱ p))

end AlgebraicGeometry.Scheme
