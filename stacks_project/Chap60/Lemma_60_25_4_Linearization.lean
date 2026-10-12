/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Pullback
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import stacks_project.Chap60.Definition_60_11_3_Crystal
public import stacks_project.Chap60.Lemma_60_9_2_Inclusion
public import stacks_project.Chap60.Lemma_60_9_2_Topos
public import stacks_project.Chap60.Proposition_60_23_1_Pushforward
public import stacks_project.Chap60.Remark_60_8_5_Functoriality
public import stacks_project.Chap60.«60_10_0_1_CrystallineSheaf»

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

/-- Zariski direct image of abelian sheaves along a scheme morphism. -/
def zariskiAbelianPushforward {X' X : Scheme.{u}} (f : X' ⟶ X) :
    Sheaf X'.smallZariskiTopology AddCommGrpCat.{u} ⥤
      Sheaf X.smallZariskiTopology AddCommGrpCat.{u} :=
  (smallZariskiPullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
    X.smallZariskiTopology X'.smallZariskiTopology

/-- Zariski direct image is continuous sheaf pushforward along small-Zariski base change. -/
theorem zariskiAbelianPushforward_eq {X' X : Scheme.{u}} (f : X' ⟶ X) :
    zariskiAbelianPushforward f =
      (smallZariskiPullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
        X.smallZariskiTopology X'.smallZariskiTopology :=
  sorry

/-- Zariski direct image of abelian sheaves is additive. -/
instance zariskiAbelianPushforward_additive {X' X : Scheme.{u}} (f : X' ⟶ X) :
    (zariskiAbelianPushforward f).Additive :=
  sorry

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {S : Scheme.{u}} (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))

/-- The structure sheaf `𝒪_{X/S}` on `Cris(X/S)`, sending a thickening to the
global sections of its thickening scheme. -/
def smallCrystallineStructureSheaf :
    Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) RingCat.{u} :=
  ⟨Scheme.Site.structurePresheaf (smallThickeningFunctor S I γ h_compatible X x₀),
    sorry⟩

/-- The structure sheaf of `Cris(X/S)` is the global-sections sheaf of the
small thickening functor. -/
theorem smallCrystallineStructureSheaf_eq :
    smallCrystallineStructureSheaf I γ h_compatible s x₀ h_p =
      ⟨Scheme.Site.structurePresheaf
        (smallThickeningFunctor S I γ h_compatible X x₀), sorry⟩ :=
  sorry

/-- The identity morphism of a divided-power scheme over `ℤ_(p)`. -/
def idDividedPowerSchemeHom :
    DividedPowerSchemeHom I I s s where
  base := 𝟙 S
  zeroFiberMap := 𝟙 I.subscheme
  zeroFiber_comm := sorry
  base_over := sorry
  ideal_compatible := sorry

/-- The identity setup morphism has underlying map `𝟙 S`. -/
theorem idDividedPowerSchemeHom_base :
    (idDividedPowerSchemeHom I s).base = 𝟙 S :=
  sorry

/-- Identity divided-power compatibility on affine opens. -/
theorem id_dividedPowers_compatible :
    ∀ (V W : S.affineOpens) (hVW : W.1 ≤ (𝟙 S) ⁻¹ᵁ V.1),
      (γ V).IsDPMorphism (γ W) ((𝟙 S : S ⟶ S).appLE V W hVW).hom :=
  sorry

variable {X' : Scheme.{u}} (x'₀ : X' ⟶ I.subscheme)
variable (f : X' ⟶ X) (h_over : f ≫ x₀ = x'₀)
variable (h_p' : ∀ U : X'.affineOpens, IsNilpotent (p : Γ(X', U)))

/-- The relative crystalline site functor of `f` over the identity of `(S, I, γ)`. -/
abbrev relativeCrystallineFunctor :
    RelativeCRIS S I γ h_compatible X' x'₀ ⥤
      RelativeCRIS S I γ h_compatible X x₀ :=
  (CrystallineFunctor.of f (idDividedPowerSchemeHom I s)
      (h_over.trans (Category.comp_id x'₀).symm) h_p' h_p
      (id_dividedPowers_compatible I γ)).toRelativeFunctor

/-- Unfolding of `relativeCrystallineFunctor` as `CrystallineFunctor.of f id_S`. -/
theorem relativeCrystallineFunctor_eq :
    relativeCrystallineFunctor I γ h_compatible s x₀ h_p x'₀ f h_over h_p' =
      (CrystallineFunctor.of f (idDividedPowerSchemeHom I s)
          (h_over.trans (Category.comp_id x'₀).symm) h_p' h_p
          (id_dividedPowers_compatible I γ)).toRelativeFunctor :=
  sorry

/-- The relative crystalline functor is continuous for the Zariski crystalline topologies. -/
instance relativeCrystallineFunctor_isContinuous :
    (relativeCrystallineFunctor I γ h_compatible s x₀ h_p x'₀ f h_over h_p').IsContinuous
      (crystallineZariskiTopology S I γ h_compatible X' x'₀)
      (crystallineZariskiTopology S I γ h_compatible X x₀) :=
  crystallineFunctor_isContinuous I I γ γ h_compatible h_compatible s s x'₀ x₀ f
    (idDividedPowerSchemeHom I s) (h_over.trans (Category.comp_id x'₀).symm)
    (id_dividedPowers_compatible I γ) h_p' h_p

/-- The relative crystalline functor is cocontinuous for the Zariski crystalline topologies. -/
instance relativeCrystallineFunctor_isCocontinuous :
    (relativeCrystallineFunctor I γ h_compatible s x₀ h_p x'₀ f h_over h_p').IsCocontinuous
      (crystallineZariskiTopology S I γ h_compatible X' x'₀)
      (crystallineZariskiTopology S I γ h_compatible X x₀) :=
  crystallineFunctor_isCocontinuous I I γ γ h_compatible h_compatible s s x'₀ x₀ f
    (idDividedPowerSchemeHom I s) (h_over.trans (Category.comp_id x'₀).symm)
    (id_dividedPowers_compatible I γ) h_p' h_p

/-- Inverse image of abelian sheaves along `f_cris`. -/
def crystallineAbelianPullback
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) AddCommGrpCat.{u}]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X' x'₀) AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X' x'₀).op.HasPointwiseRightKanExtension P]
    [∀ P : (RelativeCRIS S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (relativeCrystallineFunctor I γ h_compatible s x₀ h_p x'₀ f h_over
          h_p').op.HasPointwiseRightKanExtension P] :
    Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u} ⥤
      Sheaf (smallCrystallineTopology p S I γ h_compatible s X' x'₀ h_p') AddCommGrpCat.{u} :=
  (smallCrystallineInclusion S I γ h_compatible X x₀).sheafPullback
      AddCommGrpCat.{u}
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (crystallineZariskiTopology S I γ h_compatible X x₀) ⋙
    ((relativeCrystallineFunctor I γ h_compatible s x₀ h_p x'₀ f h_over
          h_p').sheafPushforwardContinuous AddCommGrpCat.{u}
        (crystallineZariskiTopology S I γ h_compatible X' x'₀)
        (crystallineZariskiTopology S I γ h_compatible X x₀) ⋙
      (smallCrystallineInclusion S I γ h_compatible X' x'₀).sheafPushforwardContinuous
        AddCommGrpCat.{u}
        (smallCrystallineTopology p S I γ h_compatible s X' x'₀ h_p')
        (crystallineZariskiTopology S I γ h_compatible X' x'₀))

/-- `f_cris^*` is the composite of `π_X⁻¹`, relative continuous pushforward, and `π_{X',*}`. -/
theorem crystallineAbelianPullback_eq
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) AddCommGrpCat.{u}]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X' x'₀) AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X' x'₀).op.HasPointwiseRightKanExtension P]
    [∀ P : (RelativeCRIS S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (relativeCrystallineFunctor I γ h_compatible s x₀ h_p x'₀ f h_over
          h_p').op.HasPointwiseRightKanExtension P] :
    crystallineAbelianPullback I γ h_compatible s x₀ h_p x'₀ f h_over h_p' =
      (smallCrystallineInclusion S I γ h_compatible X x₀).sheafPullback
          AddCommGrpCat.{u}
          (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
          (crystallineZariskiTopology S I γ h_compatible X x₀) ⋙
        ((relativeCrystallineFunctor I γ h_compatible s x₀ h_p x'₀ f h_over
              h_p').sheafPushforwardContinuous AddCommGrpCat.{u}
            (crystallineZariskiTopology S I γ h_compatible X' x'₀)
            (crystallineZariskiTopology S I γ h_compatible X x₀) ⋙
          (smallCrystallineInclusion S I γ h_compatible X' x'₀).sheafPushforwardContinuous
            AddCommGrpCat.{u}
            (smallCrystallineTopology p S I γ h_compatible s X' x'₀ h_p')
            (crystallineZariskiTopology S I γ h_compatible X' x'₀)) :=
  sorry

/-- Direct image of abelian sheaves along `f_cris`. -/
def crystallineAbelianCrisPushforward
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) AddCommGrpCat.{u}]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X' x'₀) AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X' x'₀).op.HasPointwiseRightKanExtension P]
    [∀ P : (RelativeCRIS S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (relativeCrystallineFunctor I γ h_compatible s x₀ h_p x'₀ f h_over
          h_p').op.HasPointwiseRightKanExtension P] :
    Sheaf (smallCrystallineTopology p S I γ h_compatible s X' x'₀ h_p') AddCommGrpCat.{u} ⥤
      Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u} :=
  ((smallCrystallineInclusion S I γ h_compatible X' x'₀).sheafPushforwardCocontinuous
        AddCommGrpCat.{u}
        (smallCrystallineTopology p S I γ h_compatible s X' x'₀ h_p')
        (crystallineZariskiTopology S I γ h_compatible X' x'₀) ⋙
      (relativeCrystallineFunctor I γ h_compatible s x₀ h_p x'₀ f h_over
          h_p').sheafPushforwardCocontinuous AddCommGrpCat.{u}
        (crystallineZariskiTopology S I γ h_compatible X' x'₀)
        (crystallineZariskiTopology S I γ h_compatible X x₀)) ⋙
    (smallCrystallineInclusion S I γ h_compatible X x₀).sheafPushforwardContinuous
      AddCommGrpCat.{u}
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (crystallineZariskiTopology S I γ h_compatible X x₀)

/-- `f_cris_*` is the composite of `i_{X',*}`, relative cocontinuous pushforward, and `π_{X,*}`. -/
theorem crystallineAbelianCrisPushforward_eq
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) AddCommGrpCat.{u}]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X' x'₀) AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X' x'₀).op.HasPointwiseRightKanExtension P]
    [∀ P : (RelativeCRIS S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (relativeCrystallineFunctor I γ h_compatible s x₀ h_p x'₀ f h_over
          h_p').op.HasPointwiseRightKanExtension P] :
    crystallineAbelianCrisPushforward I γ h_compatible s x₀ h_p x'₀ f h_over h_p' =
      ((smallCrystallineInclusion S I γ h_compatible X' x'₀).sheafPushforwardCocontinuous
            AddCommGrpCat.{u}
            (smallCrystallineTopology p S I γ h_compatible s X' x'₀ h_p')
            (crystallineZariskiTopology S I γ h_compatible X' x'₀) ⋙
          (relativeCrystallineFunctor I γ h_compatible s x₀ h_p x'₀ f h_over
              h_p').sheafPushforwardCocontinuous AddCommGrpCat.{u}
            (crystallineZariskiTopology S I γ h_compatible X' x'₀)
            (crystallineZariskiTopology S I γ h_compatible X x₀)) ⋙
        (smallCrystallineInclusion S I γ h_compatible X x₀).sheafPushforwardContinuous
          AddCommGrpCat.{u}
          (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
          (crystallineZariskiTopology S I γ h_compatible X x₀) :=
  sorry

/-- The adjunction `f_cris^* ⊣ f_cris_*` on abelian sheaves, as the composite of
the canonical sheaf adjunctions of `π_X`, `f_CRIS`, and `π_{X'}`. -/
def crystallineAbelianCrisAdjunction
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) AddCommGrpCat.{u}]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X' x'₀) AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X' x'₀).op.HasPointwiseRightKanExtension P]
    [∀ P : (RelativeCRIS S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (relativeCrystallineFunctor I γ h_compatible s x₀ h_p x'₀ f h_over
          h_p').op.HasPointwiseRightKanExtension P] :
    crystallineAbelianPullback I γ h_compatible s x₀ h_p x'₀ f h_over h_p' ⊣
      crystallineAbelianCrisPushforward I γ h_compatible s x₀ h_p x'₀ f h_over h_p' :=
  ((smallCrystallineInclusion S I γ h_compatible X x₀).sheafAdjunctionContinuous
        AddCommGrpCat.{u}
        (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
        (crystallineZariskiTopology S I γ h_compatible X x₀)).comp
    (((relativeCrystallineFunctor I γ h_compatible s x₀ h_p x'₀ f h_over
            h_p').sheafAdjunctionCocontinuous AddCommGrpCat.{u}
          (crystallineZariskiTopology S I γ h_compatible X' x'₀)
          (crystallineZariskiTopology S I γ h_compatible X x₀)).comp
      ((smallCrystallineInclusion S I γ h_compatible X' x'₀).sheafAdjunctionCocontinuous
        AddCommGrpCat.{u}
        (smallCrystallineTopology p S I γ h_compatible s X' x'₀ h_p')
        (crystallineZariskiTopology S I γ h_compatible X' x'₀)))

/-- The adjunction `f_cris^* ⊣ f_cris_*` is the composite of the three sheaf adjunctions. -/
theorem crystallineAbelianCrisAdjunction_eq
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) AddCommGrpCat.{u}]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X' x'₀) AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X' x'₀).op.HasPointwiseRightKanExtension P]
    [∀ P : (RelativeCRIS S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (relativeCrystallineFunctor I γ h_compatible s x₀ h_p x'₀ f h_over
          h_p').op.HasPointwiseRightKanExtension P] :
    crystallineAbelianCrisAdjunction I γ h_compatible s x₀ h_p x'₀ f h_over h_p' =
      ((smallCrystallineInclusion S I γ h_compatible X x₀).sheafAdjunctionContinuous
            AddCommGrpCat.{u}
            (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
            (crystallineZariskiTopology S I γ h_compatible X x₀)).comp
        (((relativeCrystallineFunctor I γ h_compatible s x₀ h_p x'₀ f h_over
                h_p').sheafAdjunctionCocontinuous AddCommGrpCat.{u}
              (crystallineZariskiTopology S I γ h_compatible X' x'₀)
              (crystallineZariskiTopology S I γ h_compatible X x₀)).comp
          ((smallCrystallineInclusion S I γ h_compatible X' x'₀).sheafAdjunctionCocontinuous
            AddCommGrpCat.{u}
            (smallCrystallineTopology p S I γ h_compatible s X' x'₀ h_p')
            (crystallineZariskiTopology S I γ h_compatible X' x'₀))) :=
  sorry

/-- The pullback `F' = f_cris^* F` of a crystal as an abelian sheaf on `Cris(X'/S)`. -/
def crystallinePullback
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) AddCommGrpCat.{u}]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X' x'₀) AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X' x'₀).op.HasPointwiseRightKanExtension P]
    [∀ P : (RelativeCRIS S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (relativeCrystallineFunctor I γ h_compatible s x₀ h_p x'₀ f h_over
          h_p').op.HasPointwiseRightKanExtension P]
    (F : SheafOfModules (smallCrystallineStructureSheaf I γ h_compatible s x₀ h_p)) :
    Sheaf (smallCrystallineTopology p S I γ h_compatible s X' x'₀ h_p') AddCommGrpCat.{u} :=
  (crystallineAbelianPullback I γ h_compatible s x₀ h_p x'₀ f h_over h_p').obj
    ((SheafOfModules.toSheaf _).obj F)

/-- Unfolding of `crystallinePullback` as `f_cris^*` of the underlying abelian sheaf. -/
theorem crystallinePullback_eq
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) AddCommGrpCat.{u}]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X' x'₀) AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X' x'₀).op.HasPointwiseRightKanExtension P]
    [∀ P : (RelativeCRIS S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (relativeCrystallineFunctor I γ h_compatible s x₀ h_p x'₀ f h_over
          h_p').op.HasPointwiseRightKanExtension P]
    (F : SheafOfModules (smallCrystallineStructureSheaf I γ h_compatible s x₀ h_p)) :
    crystallinePullback I γ h_compatible s x₀ h_p x'₀ f h_over h_p' F =
      (crystallineAbelianPullback I γ h_compatible s x₀ h_p x'₀ f h_over h_p').obj
        ((SheafOfModules.toSheaf _).obj F) :=
  sorry

/-- The unit of `f_cris^* ⊣ f_cris_*` on the abelian sheaf underlying a crystal. -/
def crystallineCrisUnitApp
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) AddCommGrpCat.{u}]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X' x'₀) AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X' x'₀).op.HasPointwiseRightKanExtension P]
    [∀ P : (RelativeCRIS S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (relativeCrystallineFunctor I γ h_compatible s x₀ h_p x'₀ f h_over
          h_p').op.HasPointwiseRightKanExtension P]
    (F : SheafOfModules (smallCrystallineStructureSheaf I γ h_compatible s x₀ h_p)) :
    (SheafOfModules.toSheaf _).obj F ⟶
      (crystallineAbelianCrisPushforward I γ h_compatible s x₀ h_p x'₀ f h_over h_p').obj
        (crystallinePullback I γ h_compatible s x₀ h_p x'₀ f h_over h_p' F) :=
  (crystallineAbelianCrisAdjunction I γ h_compatible s x₀ h_p x'₀ f h_over h_p').unit.app
    ((SheafOfModules.toSheaf _).obj F)

/-- The unit component is the adjunction unit of `f_cris^* ⊣ f_cris_*`. -/
theorem crystallineCrisUnitApp_eq
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) AddCommGrpCat.{u}]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X' x'₀) AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X' x'₀).op.HasPointwiseRightKanExtension P]
    [∀ P : (RelativeCRIS S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (relativeCrystallineFunctor I γ h_compatible s x₀ h_p x'₀ f h_over
          h_p').op.HasPointwiseRightKanExtension P]
    (F : SheafOfModules (smallCrystallineStructureSheaf I γ h_compatible s x₀ h_p)) :
    crystallineCrisUnitApp I γ h_compatible s x₀ h_p x'₀ f h_over h_p' F =
      (crystallineAbelianCrisAdjunction I γ h_compatible s x₀ h_p x'₀ f h_over h_p').unit.app
        ((SheafOfModules.toSheaf _).obj F) :=
  sorry

/-- Canonical comparison `Ru_{X/S,*} F ⟶ Ru_{X/S,*}(f_cris_* F')` induced by the unit of
`f_cris^* ⊣ f_cris_*`. -/
def linearizationComparison
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) AddCommGrpCat.{u}]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X' x'₀) AddCommGrpCat.{u}]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X' x'₀).op.HasPointwiseRightKanExtension P]
    [∀ P : (RelativeCRIS S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (relativeCrystallineFunctor I γ h_compatible s x₀ h_p x'₀ f h_over
          h_p').op.HasPointwiseRightKanExtension P]
    [HasDerivedCategory
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})]
    [HasDerivedCategory (Sheaf X.smallZariskiTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})]
    (F : SheafOfModules (smallCrystallineStructureSheaf I γ h_compatible s x₀ h_p)) :
    derivedSmallCrystallinePushforward_obj I γ h_compatible s x₀ h_p
        ((SheafOfModules.toSheaf _).obj F) ⟶
      derivedSmallCrystallinePushforward_obj I γ h_compatible s x₀ h_p
        ((crystallineAbelianCrisPushforward I γ h_compatible s x₀ h_p x'₀ f h_over h_p').obj
          (crystallinePullback I γ h_compatible s x₀ h_p x'₀ f h_over h_p' F)) :=
  (derivedSmallCrystallinePushforward I γ h_compatible s x₀ h_p).map
    ((DerivedCategory.singleFunctor
        (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
          AddCommGrpCat.{u}) 0).map
      (crystallineCrisUnitApp I γ h_compatible s x₀ h_p x'₀ f h_over h_p' F))

/-- The comparison is `Ru_{X/S,*}` applied to the concentrated unit of `f_cris`. -/
theorem linearizationComparison_spec
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) AddCommGrpCat.{u}]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X' x'₀) AddCommGrpCat.{u}]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X' x'₀).op.HasPointwiseRightKanExtension P]
    [∀ P : (RelativeCRIS S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (relativeCrystallineFunctor I γ h_compatible s x₀ h_p x'₀ f h_over
          h_p').op.HasPointwiseRightKanExtension P]
    [HasDerivedCategory
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})]
    [HasDerivedCategory (Sheaf X.smallZariskiTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})]
    (F : SheafOfModules (smallCrystallineStructureSheaf I γ h_compatible s x₀ h_p)) :
    linearizationComparison I γ h_compatible s x₀ h_p x'₀ f h_over h_p' F =
      (derivedSmallCrystallinePushforward I γ h_compatible s x₀ h_p).map
        ((DerivedCategory.singleFunctor
            (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
              AddCommGrpCat.{u}) 0).map
          (crystallineCrisUnitApp I γ h_compatible s x₀ h_p x'₀ f h_over h_p' F)) :=
  sorry

/-- The source packaging `f_* u_{X'/S,*} F'` is isomorphic to
`u_{X/S,*}(f_cris_* F')` after the commuting square of `u` and `f`. -/
theorem linearizationComparison_zariskiPushforward_iso
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) AddCommGrpCat.{u}]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X' x'₀) AddCommGrpCat.{u}]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X' x'₀ h_p') AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (forgetfulFunctor p S I γ h_compatible s X' x'₀ h_p').op.HasPointwiseRightKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X' x'₀).op.HasPointwiseRightKanExtension P]
    [∀ P : (RelativeCRIS S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (relativeCrystallineFunctor I γ h_compatible s x₀ h_p x'₀ f h_over
          h_p').op.HasPointwiseRightKanExtension P]
    (F : SheafOfModules (smallCrystallineStructureSheaf I γ h_compatible s x₀ h_p)) :
    Nonempty
      ((smallCrystallinePushforward I γ h_compatible s x₀ h_p).obj
          ((crystallineAbelianCrisPushforward I γ h_compatible s x₀ h_p x'₀ f
              h_over h_p').obj
            (crystallinePullback I γ h_compatible s x₀ h_p x'₀ f h_over h_p' F)) ≅
        (zariskiAbelianPushforward f).obj
          ((smallCrystallinePushforward I γ h_compatible s x'₀ h_p').obj
            (crystallinePullback I γ h_compatible s x₀ h_p x'₀ f h_over h_p' F))) :=
  sorry

end AlgebraicGeometry.Scheme.Crystalline
