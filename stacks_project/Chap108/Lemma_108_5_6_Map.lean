module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Lemma_66_29_2
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap99.«99_8_1_1_Functor»

/-!
# The Quot functor map along an open immersion

An open immersion `j : X ⟶ Y` of algebraic spaces over `B` induces a comparison
`X_T ⟶ Y_T` on fibres and a natural transformation
`quot (j ≫ y) (j^* G) ⟶ quot y G`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X Y B : AlgebraicSpace S}

/-- The comparison `X_T ⟶ Y_T` induced by `j : X ⟶ Y` over `B`. -/
def openFiberComparison (j : X ⟶ Y) (y : Y ⟶ B) (σ : SchemesOver B) :
    fiber (j ≫ y) σ ⟶ fiber y σ :=
  pullback.map (j ≫ y) σ.hom y σ.hom j
    (𝟙 ((ofOverFunctor S).obj σ.left)) (𝟙 B) (Category.comp_id (j ≫ y))
    ((Category.comp_id σ.hom).trans (Category.id_comp σ.hom).symm)

/-- The fibre comparison commutes with the projections to `X` and `Y`. -/
theorem openFiberComparison_fst (j : X ⟶ Y) (y : Y ⟶ B) (σ : SchemesOver B) :
    openFiberComparison j y σ ≫ pullback.fst y σ.hom =
      pullback.fst (j ≫ y) σ.hom ≫ j :=
  pullback.lift_fst _ _ _

/-- The fibre comparison commutes with the projections to the test scheme. -/
theorem openFiberComparison_snd (j : X ⟶ Y) (y : Y ⟶ B) (σ : SchemesOver B) :
    openFiberComparison j y σ ≫ pullback.snd y σ.hom =
      pullback.snd (j ≫ y) σ.hom ≫ 𝟙 ((ofOverFunctor S).obj σ.left) :=
  pullback.lift_snd _ _ _

/-- The fibre comparison is the map of pullbacks induced by `j` and the identity
on the test scheme. -/
theorem openFiberComparison_spec (j : X ⟶ Y) (y : Y ⟶ B) (σ : SchemesOver B) :
    openFiberComparison j y σ ≫ pullback.fst y σ.hom =
        pullback.fst (j ≫ y) σ.hom ≫ j ∧
      openFiberComparison j y σ ≫ pullback.snd y σ.hom =
        pullback.snd (j ≫ y) σ.hom :=
  ⟨openFiberComparison_fst j y σ,
    (openFiberComparison_snd j y σ).trans
      (Category.comp_id (pullback.snd (j ≫ y) σ.hom))⟩

/-- The fibre comparison of an open immersion is an open immersion. -/
instance instIsOpenImmersion_openFiberComparison (j : X ⟶ Y) (y : Y ⟶ B)
    (σ : SchemesOver B) [IsOpenImmersion j] :
    IsOpenImmersion (openFiberComparison j y σ) :=
  sorry

/-- The identification `F_T ≅ j_T^* G_T` for `F = j^* G`. -/
def fiberPullbackIso (j : X ⟶ Y) (y : Y ⟶ B) (G : Y.Modules)
    (σ : SchemesOver B) :
    fiberF (j ≫ y) ((Modules.pullback j).obj G) σ ≅
      (Modules.pullback (openFiberComparison j y σ)).obj (fiberF y G σ) :=
  ((Modules.pullbackComp (openFiberComparison j y σ) (pullback.fst y σ.hom) ≪≫
      eqToIso (congrArg Modules.pullback (openFiberComparison_fst j y σ)) ≪≫
      (Modules.pullbackComp (pullback.fst (j ≫ y) σ.hom) j).symm).symm).app G

/-- The forward map of `fiberPullbackIso` is the inverse of the pullback-composition
comparison along the fibre square. -/
theorem fiberPullbackIso_hom (j : X ⟶ Y) (y : Y ⟶ B) (G : Y.Modules)
    (σ : SchemesOver B) :
    (fiberPullbackIso j y G σ).hom =
      ((Modules.pullbackComp (openFiberComparison j y σ) (pullback.fst y σ.hom) ≪≫
          eqToIso (congrArg Modules.pullback (openFiberComparison_fst j y σ)) ≪≫
          (Modules.pullbackComp (pullback.fst (j ≫ y) σ.hom) j).symm).symm).hom.app G :=
  sorry

/-- Pushforward of a Quot-point `F_T ⟶ Q` of `F = j^* G` along `j_T` yields a
Quot-point `G_T ⟶ j_{T,*} Q`. -/
def QuotPoint.openPushforward (j : X ⟶ Y) (y : Y ⟶ B) {σ : SchemesOver B}
    [IsOpenImmersion j] [Separated (j ≫ y)] [FinitePresentation (j ≫ y)]
    [Separated y] [FinitePresentation y]
    {G : Y.Modules} [G.IsQuasicoherent]
    (Q : QuotPoint (j ≫ y) ((Modules.pullback j).obj G) σ) :
    QuotPoint y G σ :=
  let jT := openFiberComparison j y σ
  QuotPoint.ofEpi y G σ ((Modules.pushforward jT).obj Q.point.module)
    ((Modules.pullbackPushforwardAdjunction jT).unit.app (fiberF y G σ) ≫
      (Modules.pushforward jT).map
        ((fiberPullbackIso j y G σ).inv ≫ Q.point.map))
    sorry sorry sorry sorry sorry

/-- The underlying module of a pushed Quot-point is `j_{T,*} Q`. -/
theorem QuotPoint.openPushforward_module (j : X ⟶ Y) (y : Y ⟶ B) {σ : SchemesOver B}
    [IsOpenImmersion j] [Separated (j ≫ y)] [FinitePresentation (j ≫ y)]
    [Separated y] [FinitePresentation y]
    {G : Y.Modules} [G.IsQuasicoherent]
    (Q : QuotPoint (j ≫ y) ((Modules.pullback j).obj G) σ) :
    (QuotPoint.openPushforward j y Q).point.module =
      (Modules.pushforward (openFiberComparison j y σ)).obj Q.point.module :=
  sorry

/-- The quotient map of a pushed Quot-point is the adjunction unit
`G_T ⟶ j_{T,*} j_T^* G_T` followed by `j_{T,*} (j_T^* G_T ⟶ Q)`. -/
theorem QuotPoint.openPushforward_map (j : X ⟶ Y) (y : Y ⟶ B) {σ : SchemesOver B}
    [IsOpenImmersion j] [Separated (j ≫ y)] [FinitePresentation (j ≫ y)]
    [Separated y] [FinitePresentation y]
    {G : Y.Modules} [G.IsQuasicoherent]
    (Q : QuotPoint (j ≫ y) ((Modules.pullback j).obj G) σ) :
    (QuotPoint.openPushforward j y Q).point.map =
      (Modules.pullbackPushforwardAdjunction
          (openFiberComparison j y σ)).unit.app (fiberF y G σ) ≫
        (Modules.pushforward (openFiberComparison j y σ)).map
          ((fiberPullbackIso j y G σ).inv ≫ Q.point.map) :=
  sorry

/-- A pushed Quot-point is the epimorphism `G_T ⟶ j_{T,*} Q` obtained from
`F_T ⟶ Q` by the unit of `j_T^* ⊣ j_{T,*}` and `j_{T,*}`. -/
theorem QuotPoint.openPushforward_spec (j : X ⟶ Y) (y : Y ⟶ B) {σ : SchemesOver B}
    [IsOpenImmersion j] [Separated (j ≫ y)] [FinitePresentation (j ≫ y)]
    [Separated y] [FinitePresentation y]
    {G : Y.Modules} [G.IsQuasicoherent]
    (Q : QuotPoint (j ≫ y) ((Modules.pullback j).obj G) σ) :
    (QuotPoint.openPushforward j y Q).point.module =
        (Modules.pushforward (openFiberComparison j y σ)).obj Q.point.module ∧
      (QuotPoint.openPushforward j y Q).point.map =
        (Modules.pullbackPushforwardAdjunction
            (openFiberComparison j y σ)).unit.app (fiberF y G σ) ≫
          (Modules.pushforward (openFiberComparison j y σ)).map
            ((fiberPullbackIso j y G σ).inv ≫ Q.point.map) :=
  sorry

/-- Kernel identification is preserved by fibrewise pushforward of Quot-points
along an open immersion. -/
theorem Rel_openPushforward (j : X ⟶ Y) (y : Y ⟶ B) (G : Y.Modules)
    [IsOpenImmersion j] [Separated (j ≫ y)] [FinitePresentation (j ≫ y)]
    [Separated y] [FinitePresentation y]
    [G.IsQuasicoherent] (σ : SchemesOver B) :
    ∀ (Q₁ Q₂ : QuotPoint (j ≫ y) ((Modules.pullback j).obj G) σ),
      (quotSetoid (j ≫ y) ((Modules.pullback j).obj G) σ).r Q₁ Q₂ →
        (quotSetoid y G σ).r (QuotPoint.openPushforward j y Q₁)
          (QuotPoint.openPushforward j y Q₂) :=
  sorry

/-- The natural transformation `Quot_{F/X/B} ⟶ Quot_{G/Y/B}` induced by an open
immersion `j : X ⟶ Y` with `F = j^* G`. -/
def openMap (j : X ⟶ Y) (y : Y ⟶ B) (G : Y.Modules)
    [IsOpenImmersion j] [Separated (j ≫ y)] [FinitePresentation (j ≫ y)]
    [Separated y] [FinitePresentation y]
    [G.IsQuasicoherent] :
    quot (j ≫ y) ((Modules.pullback j).obj G) ⟶ quot y G where
  app σ :=
    TypeCat.ofHom
      (_root_.Quotient.map
        (fun Q : QuotPoint (j ≫ y) ((Modules.pullback j).obj G) σ.unop ↦
          QuotPoint.openPushforward j y Q)
        (Rel_openPushforward j y G σ.unop))
  naturality := sorry

/-- The component of `openMap j y G` at a scheme over `B` is the quotient map of
`QuotPoint.openPushforward`. -/
theorem openMap_app (j : X ⟶ Y) (y : Y ⟶ B) (G : Y.Modules)
    [IsOpenImmersion j] [Separated (j ≫ y)] [FinitePresentation (j ≫ y)]
    [Separated y] [FinitePresentation y]
    [G.IsQuasicoherent] (σ : (SchemesOver B)ᵒᵖ) :
    (openMap j y G).app σ =
      TypeCat.ofHom
        (_root_.Quotient.map
          (fun Q : QuotPoint (j ≫ y) ((Modules.pullback j).obj G) σ.unop ↦
            QuotPoint.openPushforward j y Q)
          (Rel_openPushforward j y G σ.unop)) :=
  sorry

/-- A morphism of `Type (u + 1)` functors on schemes over `B` is an open
immersion when it is relatively representable with respect to `uliftYoneda` and
every represented pullback is an open immersion of schemes. -/
def IsOpenImmersionOnSchemesOver {F G : (SchemesOver B)ᵒᵖ ⥤ Type (u + 1)}
    (φ : F ⟶ G) : Prop :=
  let P : MorphismProperty (SchemesOver B) :=
    fun _ _ h ↦ AlgebraicGeometry.IsOpenImmersion h.left.left
  P.relative uliftYoneda.{u + 1} φ

/-- Open immersions of Quot-sized functors are relatively representable
`uliftYoneda` morphisms whose represented scheme maps are open immersions. -/
theorem isOpenImmersionOnSchemesOver_iff {F G : (SchemesOver B)ᵒᵖ ⥤ Type (u + 1)}
    (φ : F ⟶ G) :
    IsOpenImmersionOnSchemesOver φ ↔
      uliftYoneda.{u + 1}.relativelyRepresentable φ ∧
        ∀ ⦃σ τ : SchemesOver B⦄ (ξ : uliftYoneda.{u + 1}.obj σ ⟶ G)
          (fst : uliftYoneda.{u + 1}.obj τ ⟶ F) (snd : τ ⟶ σ),
          IsPullback fst (uliftYoneda.{u + 1}.map snd) φ ξ →
            AlgebraicGeometry.IsOpenImmersion snd.left.left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
