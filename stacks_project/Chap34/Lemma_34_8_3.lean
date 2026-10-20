module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Ph.Refinement
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

/- Lemma 34.8.3 (1): every Zariski open cover of an affine scheme admits a
refinement by a standard ph covering. -/
@[stacks 0DBF] #check
  (AlgebraicGeometry.StandardPhCovering.exists_refinement_of_openCover :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine T]
      (𝒰 : T.OpenCover.{v}),
      ∃ Φ : AlgebraicGeometry.StandardPhCovering T,
        ∀ j : Fin Φ.m, ∃ i : 𝒰.I₀, ∃ g : Φ.obj j ⟶ 𝒰.X i,
          g ≫ 𝒰.f i = Φ.map j)

/- Lemma 34.8.3 (2): a dependent composite of standard ph coverings of an
affine scheme admits a refinement by a standard ph covering. -/
@[stacks 0DBF] #check
  (AlgebraicGeometry.StandardPhCovering.exists_refinement_of_comp :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine T]
      (Φ : AlgebraicGeometry.StandardPhCovering T)
      (Ψ : ∀ j : Fin Φ.m, AlgebraicGeometry.StandardPhCovering (Φ.obj j)),
      ∃ Ω : AlgebraicGeometry.StandardPhCovering T,
        ∀ k : Fin Ω.m,
          ∃ p : Sigma fun j : Fin Φ.m ↦ Fin (Ψ j).m,
            ∃ g : Ω.obj k ⟶ (Ψ p.1).obj p.2,
              g ≫ (Ψ p.1).map p.2 ≫ Φ.map p.1 = Ω.map k)
