module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap65.Lemma_65_12_2
public import stacks_project.Chap65.Lemma_65_12_3_Pullback
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap69.Lemma_69_11_2_Flat_base_change_BaseChange
public import stacks_project.Chap71.Lemma_71_12_2_Map

/-!
# Composition of relative projective spectrum maps of algebraic spaces

The composite domain is the inverse image `r_ψ ⁻¹(U(φ))`, the restricted morphism is
`r_φ ∘ r_ψ` on that open, and the degreewise comparison is `θ_ψ ∘ r_ψ^* θ_φ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProjMap

variable {S : Scheme.{u}} {X P Q R : AlgebraicSpace S}
variable {πP : P ⟶ X} {πQ : Q ⟶ X} {πR : R ⟶ X}
variable {𝒜 ℬ 𝒞 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
variable [𝒜.IsQuasicoherent] [ℬ.IsQuasicoherent] [𝒞.IsQuasicoherent]
variable {twistP : ℤ → P.Modules} {twistQ : ℤ → Q.Modules} {twistR : ℤ → R.Modules}
variable {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ} {ψ : GradedAlgebraSheaf.Hom.{u + 1, u} ℬ 𝒞}

/-- The inverse-image open `r_ψ ⁻¹(U(φ)) ⊂ R`, realized as the pullback of
`U(φ) ⟶ Q` along `r_ψ` and included into `R`. -/
def compDomain (rφ : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    (rψ : RelativeProjMap πQ πR ℬ 𝒞 twistQ twistR ψ) : OpenSubspace R :=
  OpenSubspace.ofι (pullback.snd rφ.domain.ι rψ.map ≫ rψ.domain.ι)

/-- The restricted composite morphism `r_φ ∘ r_ψ` on `r_ψ ⁻¹(U(φ))`. -/
def compMap (rφ : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    (rψ : RelativeProjMap πQ πR ℬ 𝒞 twistQ twistR ψ) :
    (compDomain rφ rψ).X ⟶ P :=
  pullback.fst rφ.domain.ι rψ.map ≫ rφ.map

/-- The degreewise twist comparison `θ_ψ ∘ r_ψ^* θ_φ` on the composite domain. -/
def compTheta (rφ : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    (rψ : RelativeProjMap πQ πR ℬ 𝒞 twistQ twistR ψ) (n : ℤ) :
    (Modules.pullback (compMap rφ rψ)).obj (twistP n) ⟶
      (Modules.pullback (compDomain rφ rψ).ι).obj (twistR n) :=
  let fst := pullback.fst rφ.domain.ι rψ.map
  let snd := pullback.snd rφ.domain.ι rψ.map
  (Modules.pullbackCompIso fst rφ.map).inv.app (twistP n) ≫
    (Modules.pullback fst).map (rφ.theta n) ≫
    (Modules.pullbackCartesianIso
        (IsPullback.of_hasPullback rφ.domain.ι rψ.map)).inv.app (twistQ n) ≫
    (Modules.pullback snd).map (rψ.theta n) ≫
    (Modules.pullbackCompIso snd rψ.domain.ι).hom.app (twistR n)

/-- The composite restricted morphism commutes with the structural morphisms to the
base. -/
theorem compMap_over_base (rφ : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    (rψ : RelativeProjMap πQ πR ℬ 𝒞 twistQ twistR ψ) :
    compMap rφ rψ ≫ πP = (compDomain rφ rψ).ι ≫ πR :=
  sorry

/-- The composite of two relative projective spectrum maps, indexed by the composite
graded algebra homomorphism. -/
def comp (rφ : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    (rψ : RelativeProjMap πQ πR ℬ 𝒞 twistQ twistR ψ) :
    RelativeProjMap πP πR 𝒜 𝒞 twistP twistR (GradedAlgebraSheaf.Hom.comp.{u + 1, u} φ ψ) where
  domain := compDomain rφ rψ
  map := compMap rφ rψ
  map_over_base := compMap_over_base rφ rψ
  theta := compTheta rφ rψ

/-- The domain of a composite map is the inverse-image open `r_ψ ⁻¹(U(φ))`. -/
theorem comp_domain (rφ : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    (rψ : RelativeProjMap πQ πR ℬ 𝒞 twistQ twistR ψ) :
    (comp rφ rψ).domain = compDomain rφ rψ :=
  sorry

/-- The underlying morphism of a composite map is the restricted composite
`r_φ ∘ r_ψ`. -/
theorem comp_map (rφ : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    (rψ : RelativeProjMap πQ πR ℬ 𝒞 twistQ twistR ψ) :
    (comp rφ rψ).map = compMap rφ rψ :=
  sorry

/-- The degreewise comparison of a composite map is `θ_ψ ∘ r_ψ^* θ_φ`. -/
theorem comp_theta (rφ : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    (rψ : RelativeProjMap πQ πR ℬ 𝒞 twistQ twistR ψ) (n : ℤ) :
    (comp rφ rψ).theta n = compTheta rφ rψ n :=
  sorry

/-- Composition has the specified domain, underlying morphism, and degreewise twist
comparison. -/
theorem comp_spec (rφ : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    (rψ : RelativeProjMap πQ πR ℬ 𝒞 twistQ twistR ψ) :
    (comp rφ rψ).domain = compDomain rφ rψ ∧
      (comp rφ rψ).map = compMap rφ rψ ∧
        ∀ n : ℤ, (comp rφ rψ).theta n = compTheta rφ rψ n :=
  sorry

/-- The points of the composite domain are the inverse image of `|U(φ)|` under
`r_ψ`, included into `|R|`. -/
theorem compDomain_pointsSet (rφ : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    (rψ : RelativeProjMap πQ πR ℬ 𝒞 twistQ twistR ψ) :
    (compDomain rφ rψ).pointsSet =
      Points.map rψ.domain.ι '' (Points.map rψ.map ⁻¹' rφ.domain.pointsSet) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProjMap
