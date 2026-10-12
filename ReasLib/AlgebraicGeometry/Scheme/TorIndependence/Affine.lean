/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.TorIndependence
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Tor independence of two schemes over a common base is equivalent both to Tor independence
of their section rings on every compatible triple of affine opens and to the existence of
compatible affine open covers on which this section-ring criterion holds. -/
@[stacks 0FXV]
theorem torIndependentOver_tfae_affine {S : Scheme.{u}} (X Y : Over S) :
    List.TFAE
      [ TorIndependentOver X Y
      , ∀ {W : S.Opens}, AlgebraicGeometry.IsAffineOpen W →
          ∀ {U : X.left.Opens}, AlgebraicGeometry.IsAffineOpen U →
            ∀ {V : Y.left.Opens}, AlgebraicGeometry.IsAffineOpen V →
              ∀ (hU : U ≤ X.hom ⁻¹ᵁ W) (hV : V ≤ Y.hom ⁻¹ᵁ W),
                let R := Γ(S, W)
                let A := Γ(X.left, U)
                let B := Γ(Y.left, V)
                let α : R →+* A := (X.hom.appLE W U hU).hom
                let β : R →+* B := (Y.hom.appLE W V hV).hom
                ModuleCat.Tor.IsIndependent
                  ((ModuleCat.restrictScalars α).obj (ModuleCat.of A A))
                  ((ModuleCat.restrictScalars β).obj (ModuleCat.of B B))
      , ∃ 𝒲 : S.AffineOpenCover,
          ∀ i : 𝒲.I₀,
            ∃ 𝒰 : ((𝒲.openCover.pullback₁ X.hom).X i).AffineOpenCover,
              ∃ 𝒱 : ((𝒲.openCover.pullback₁ Y.hom).X i).AffineOpenCover,
                ∀ j : 𝒰.I₀, ∀ k : 𝒱.I₀,
                  let R := Γ(𝒲.openCover.X i, ⊤)
                  let A := Γ(Spec (𝒰.X j), ⊤)
                  let B := Γ(Spec (𝒱.X k), ⊤)
                  let α : R →+* A :=
                    ((𝒰.f j ≫ 𝒲.openCover.pullbackHom X.hom i).appTop).hom
                  let β : R →+* B :=
                    ((𝒱.f k ≫ 𝒲.openCover.pullbackHom Y.hom i).appTop).hom
                  ModuleCat.Tor.IsIndependent
                    ((ModuleCat.restrictScalars α).obj (ModuleCat.of A A))
                    ((ModuleCat.restrictScalars β).obj (ModuleCat.of B B))
      ] := sorry

end AlgebraicGeometry.Scheme
