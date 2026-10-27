/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Map.Composition

/-!
# Lemma 71.12.2

Functoriality of relative Proj of algebraic spaces is transitive: the domain of
the composite is the inverse image `r_ψ ⁻¹(U(φ))`, the morphism is the restricted
composite `r_φ ∘ r_ψ`, and the twist comparison is `θ_ψ ∘ r_ψ^* θ_φ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

universe u
variable {S : Scheme.{u}} {X P Q R : AlgebraicSpace S}
variable {𝒜 ℬ 𝒞 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
variable [𝒜.IsQuasicoherent] [ℬ.IsQuasicoherent] [𝒞.IsQuasicoherent]
variable [𝒜.IsCommutative] [ℬ.IsCommutative] [𝒞.IsCommutative]
variable {πP : P ⟶ X} {πQ : Q ⟶ X} {πR : R ⟶ X}
variable {twistP : ℤ → P.Modules} {twistQ : ℤ → Q.Modules} {twistR : ℤ → R.Modules}
variable {p : RelativeProj.EtalePresentation 𝒜 πP twistP}
variable {q : RelativeProj.EtalePresentation ℬ πQ twistQ}
variable {r : RelativeProj.EtalePresentation 𝒞 πR twistR}

/- Lemma 71.12.2
The canonical map for a composite graded algebra map is the restricted composite,
including its open domain and the comparison in every integral Serre degree.
-/
@[stacks 085G] #check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.Map.canonical_comp :
  ∀ (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    (ψ : GradedAlgebraSheaf.Hom.{u + 1, u} ℬ 𝒞)
    (rφ : RelativeProj.Map p q) (rψ : RelativeProj.Map q r) (rcomp : RelativeProj.Map p r),
    rφ.IsCanonical φ → rψ.IsCanonical ψ →
    rcomp.IsCanonical (GradedAlgebraSheaf.Hom.comp.{u + 1, u} φ ψ) →
    rcomp = RelativeProj.Map.comp rφ rψ)

variable (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
variable (ψ : GradedAlgebraSheaf.Hom.{u + 1, u} ℬ 𝒞)
variable (rφ : RelativeProj.Map p q) (rψ : RelativeProj.Map q r) (rcomp : RelativeProj.Map p r)
variable (hφ : rφ.IsCanonical φ) (hψ : rψ.IsCanonical ψ)
variable (hcomp : rcomp.IsCanonical (GradedAlgebraSheaf.Hom.comp.{u + 1, u} φ ψ))

/- Lemma 71.12.2 (1)
The domain of the composite relative-Proj map is the inverse-image open
`r_ψ ⁻¹(U(φ))` in `R`.
-/
@[stacks 085G] #check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.Map.canonical_comp_domain
  φ ψ rφ rψ rcomp hφ hψ hcomp : rcomp.domain = RelativeProj.Map.compDomain rφ rψ)

/- Lemma 71.12.2 (2)
The composite morphism is `r_φ ∘ r_ψ` restricted to `U(ψ ∘ φ)`.
-/
@[stacks 085G] #check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.Map.canonical_comp_map
  φ ψ rφ rψ rcomp hφ hψ hcomp : rcomp.map =
    RelativeProj.Map.mapOnDomain
      (RelativeProj.Map.canonical_comp_domain φ ψ rφ rψ rcomp hφ hψ hcomp)
      (RelativeProj.Map.compMap rφ rψ))

/- Lemma 71.12.2 (3)
The degreewise twist comparison of the composite is `θ_ψ ∘ r_ψ^* θ_φ`.
-/
@[stacks 085G] #check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.Map.canonical_comp_theta
  φ ψ rφ rψ rcomp hφ hψ hcomp : ∀ n : ℤ,
    rcomp.theta n =
      (Modules.pullbackCongr
        (RelativeProj.Map.canonical_comp_map φ ψ rφ rψ rcomp hφ hψ hcomp)).hom.app
          (twistP n) ≫
        RelativeProj.Map.thetaOnDomain
          (RelativeProj.Map.canonical_comp_domain φ ψ rφ rψ rcomp hφ hψ hcomp)
          (RelativeProj.Map.compMap rφ rψ) n (RelativeProj.Map.compTheta rφ rψ n))

