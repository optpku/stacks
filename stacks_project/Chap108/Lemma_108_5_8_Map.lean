module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap99.«99_8_1_1_Functor»
public import stacks_project.Chap108.Lemma_108_5_1_ClosedImmersion

/-!
# Precomposition of Grothendieck Quot functors along a module surjection

A surjection `φ : F ⟶ G` of quasi-coherent modules on `X` induces a comparison
of Quot-points by precomposition with `φ_T`, and a natural transformation
`quot f G ⟶ quot f F`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Precomposition of a Quot-point `G_T ⟶ Q` with the pullback `φ_T : F_T ⟶ G_T`
yields a Quot-point `F_T ⟶ Q` of `F`. -/
def QuotPoint.precomp {f : X ⟶ B} [FinitePresentation f] {F G : X.Modules}
    {σ : SchemesOver B} (φ : F ⟶ G) [Epi φ] (Q : QuotPoint f G σ) :
    QuotPoint f F σ :=
  QuotPoint.ofEpi f F σ Q.point.module
    ((Modules.pullback (pullback.fst f σ.hom)).map φ ≫ Q.point.map)
    sorry sorry sorry sorry sorry

/-- The underlying module of a precomposed Quot-point is the original target
module `Q`. -/
theorem QuotPoint.precomp_module {f : X ⟶ B} [FinitePresentation f]
    {F G : X.Modules} {σ : SchemesOver B} (φ : F ⟶ G) [Epi φ]
    (Q : QuotPoint f G σ) :
    (QuotPoint.precomp φ Q).point.module = Q.point.module :=
  sorry

/-- The quotient map of a precomposed Quot-point is `φ_T ≫ (G_T ⟶ Q)`. -/
theorem QuotPoint.precomp_map {f : X ⟶ B} [FinitePresentation f]
    {F G : X.Modules} {σ : SchemesOver B} (φ : F ⟶ G) [Epi φ]
    (Q : QuotPoint f G σ) :
    (QuotPoint.precomp φ Q).point.map =
      (Modules.pullback (pullback.fst f σ.hom)).map φ ≫ Q.point.map :=
  sorry

/-- A precomposed Quot-point is the epimorphism `F_T ⟶ Q` obtained from
`G_T ⟶ Q` by precomposition with `φ_T`. -/
theorem QuotPoint.precomp_spec {f : X ⟶ B} [FinitePresentation f]
    {F G : X.Modules} {σ : SchemesOver B} (φ : F ⟶ G) [Epi φ]
    (Q : QuotPoint f G σ) :
    (QuotPoint.precomp φ Q).point.module = Q.point.module ∧
      (QuotPoint.precomp φ Q).point.map =
        (Modules.pullback (pullback.fst f σ.hom)).map φ ≫ Q.point.map :=
  sorry

/-- Kernel identification is preserved by precomposition of Quot-points with a
module surjection. -/
theorem Rel_precomp (f : X ⟶ B) [FinitePresentation f] {F G : X.Modules}
    (φ : F ⟶ G) [Epi φ] (σ : SchemesOver B) :
    ∀ (Q₁ Q₂ : QuotPoint f G σ),
      (quotSetoid f G σ).r Q₁ Q₂ →
        (quotSetoid f F σ).r (QuotPoint.precomp φ Q₁) (QuotPoint.precomp φ Q₂) :=
  sorry

/-- The natural transformation `Quot_{G/X/B} ⟶ Quot_{F/X/B}` induced by
precomposition with a surjection `φ : F ⟶ G` of quasi-coherent modules. -/
def precompHom (f : X ⟶ B) [FinitePresentation f] [Separated f]
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (φ : F ⟶ G) [Epi φ] :
    quot f G ⟶ quot f F where
  app σ :=
    TypeCat.ofHom
      (_root_.Quotient.map (fun Q : QuotPoint f G σ.unop ↦ QuotPoint.precomp φ Q)
        (Rel_precomp f φ σ.unop))
  naturality := sorry

/-- The component of `precompHom f φ` at a scheme over `B` is the setoid quotient
map of `QuotPoint.precomp`. -/
theorem precompHom_app (f : X ⟶ B) [FinitePresentation f] [Separated f]
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (φ : F ⟶ G) [Epi φ] (σ : (SchemesOver B)ᵒᵖ) :
    (precompHom f φ).app σ =
      TypeCat.ofHom
        (_root_.Quotient.map (fun Q : QuotPoint f G σ.unop ↦ QuotPoint.precomp φ Q)
          (Rel_precomp f φ σ.unop)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
