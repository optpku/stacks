/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import ReasLib.CategoryTheory.Homology.DoubleComplex.TotalComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Koszul.Augmentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AlternatingCech
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.GlobalSections
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Filtration.GradedPieces

/-!
# Hom-bicomplex comparison from the alternating Čech complex to derived sections

For a surjective étale morphism `f : U ⟶ X` and an injective resolution of an abelian
étale sheaf `F`, the bicomplex `Hom(K^p, I^q)` supplies the canonical maps from the
alternating Čech complex and from `Γ(X, I^•)` to the total complex in `D(Ab)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open HomologicalComplex HomologicalComplex₂ Opposite ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Negative degrees of an extended alternating Čech complex vanish. -/
theorem isZero_alternatingCechComplex_extend_of_not_nonneg {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (n : ℤ) (hn : ¬ 0 ≤ n) :
    IsZero (((alternatingCechComplex f F).extend embeddingUpNat).X n) :=
  sorry

/-- Flipped preadditive Yoneda on abelian étale sheaves preserves zero morphisms. -/
instance preadditiveYoneda_flip_smallEtale_preservesZeroMorphisms (X : AlgebraicSpace S)
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})] :
    ((preadditiveYoneda :
        Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤ _).flip).PreservesZeroMorphisms :=
  sorry

/-- Each Hom-functor `Hom(K, -)` on abelian étale sheaves preserves zero morphisms. -/
instance preadditiveYoneda_flip_obj_smallEtale_preservesZeroMorphisms (X : AlgebraicSpace S)
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    (K : (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})ᵒᵖ) :
    ((preadditiveYoneda :
        Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤ _).flip.obj K).PreservesZeroMorphisms :=
  sorry

/-- The opposite truncated Koszul complex, extended by zero from `ℕ` to `ℤ`. -/
noncomputable def koszulComplexExtend {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f] :
    CochainComplex (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})ᵒᵖ ℤ :=
  (HomologicalComplex.op (koszulComplex f)).extend embeddingUpNat

/-- A chosen injective resolution of an abelian étale sheaf. -/
noncomputable def chosenInjectiveResolution {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [hAb : Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [hF : HasInjectiveResolution F] :
    InjectiveResolution F := by
  let canonicalZero : HasZeroMorphisms
      (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) := inferInstance
  let abelianZero : HasZeroMorphisms
      (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :=
    @Preadditive.preadditiveHasZeroMorphisms _ _ hAb.toPreadditive
  have hzero : canonicalZero = abelianZero := HasZeroMorphisms.ext _ _
  let adaptedHypothesis := Eq.mp
    (congrArg (fun z ↦ @HasInjectiveResolution _ _ _ z F) hzero) hF
  exact Eq.mp (congrArg (fun z ↦ @InjectiveResolution _ _ _ z F) hzero.symm)
    (@CategoryTheory.injectiveResolution _ _ hAb F adaptedHypothesis)

/-- An injective resolution of `F`, extended by zero from `ℕ` to `ℤ`. -/
noncomputable def injectiveCocomplexExtend {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F] :
    CochainComplex (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) ℤ :=
  (chosenInjectiveResolution F).cocomplex.extend embeddingUpNat

/-- The Hom bicomplex `Hom(K^p, I^q)` of the truncated Koszul complex of `f` against an
injective resolution of `F`, indexed by `ℤ × ℤ`. -/
noncomputable def homBicomplex {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F] :
    HomologicalComplex₂ AddCommGrpCat.{u + 1} (up ℤ) (up ℤ) :=
  ((preadditiveYoneda.flip.mapBifunctorHomologicalComplex (up ℤ) (up ℤ)).obj
      (koszulComplexExtend f)).obj
    (injectiveCocomplexExtend F)

/-- Nonnegative bidegrees of the Hom bicomplex are `Hom(K^p, I^q)` in `Ab(X_étale)`. -/
noncomputable def homBicomplex_X {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F]
    (p q : ℕ) :
    ((homBicomplex f F).X p).X q ≅
      (preadditiveYoneda.obj ((chosenInjectiveResolution F).cocomplex.X q)).obj
        (op ((koszulComplex f).X p)) :=
  (preadditiveYoneda.flip.mapIso
      (extendXIso (HomologicalComplex.op (koszulComplex f)) embeddingUpNat
        (by rfl))).app
    ((injectiveCocomplexExtend F).X q) ≪≫
  (preadditiveYoneda.flip.obj (op ((koszulComplex f).X p))).mapIso
    (extendXIso (chosenInjectiveResolution F).cocomplex embeddingUpNat
      (by rfl))

/-- The Hom bicomplex of a first-quadrant Hom-diagram admits a total complex. -/
instance homBicomplex_hasTotal {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F] :
    (homBicomplex f F).HasTotal (up ℤ) :=
  fun n ↦ by infer_instance

/-- The cochain map `Čech_alt(f, F) ⟶ Hom(K^•, I^0)` induced by `F ⟶ I^0`. -/
noncomputable def alternatingCechToHomI0 {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F] :
    alternatingCechComplex f F ⟶
      alternatingCechComplex f ((chosenInjectiveResolution F).cocomplex.X 0) :=
  alternatingCechComplexMap f ((chosenInjectiveResolution F).ι.f 0)

/-- Negative degrees of the zeroth row of `Hom(K^•, I^•)` vanish. -/
theorem isZero_homBicomplex_zeroRow_of_not_nonneg {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F]
    (n : ℤ) (hn : ¬ 0 ≤ n) :
    IsZero (((homBicomplex f F).zeroRow).X n) :=
  sorry

/-- Degreewise identification of the extended alternating Čech complex of `I^0` with the
zeroth row of `Hom(K^•, I^•)`. -/
noncomputable def alternatingCechInjectiveExtendIsoZeroRow_X {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F]
    (n : ℤ) :
    ((alternatingCechComplex f
        ((chosenInjectiveResolution F).cocomplex.X 0)).extend embeddingUpNat).X n ≅
      ((homBicomplex f F).zeroRow).X n :=
  if hn : 0 ≤ n then
    extendXIso
        (alternatingCechComplex f ((chosenInjectiveResolution F).cocomplex.X 0))
        embeddingUpNat (Int.toNat_of_nonneg hn) ≪≫
      (preadditiveYoneda.flip.obj (op ((koszulComplex f).X n.toNat))).mapIso
        (extendXIso (chosenInjectiveResolution F).cocomplex embeddingUpNat
          (by rfl)).symm ≪≫
      (preadditiveYoneda.flip.mapIso
        (extendXIso (HomologicalComplex.op (koszulComplex f)) embeddingUpNat
          (Int.toNat_of_nonneg hn)).symm).app
        ((injectiveCocomplexExtend F).X 0)
  else
    { hom := 0
      inv := 0
      hom_inv_id :=
        (isZero_alternatingCechComplex_extend_of_not_nonneg f
          ((chosenInjectiveResolution F).cocomplex.X 0) n hn).eq_of_src _ _
      inv_hom_id :=
        (isZero_homBicomplex_zeroRow_of_not_nonneg f F n hn).eq_of_src _ _ }

/-- The degreewise zeroth-row identification commutes with differentials. -/
theorem alternatingCechInjectiveExtendIsoZeroRow_comm {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F]
    (i j : ℤ) (hij : (up ℤ).Rel i j) :
    (alternatingCechInjectiveExtendIsoZeroRow_X f F i).hom ≫
        ((homBicomplex f F).zeroRow).d i j =
      ((alternatingCechComplex f
          ((chosenInjectiveResolution F).cocomplex.X 0)).extend embeddingUpNat).d i j ≫
        (alternatingCechInjectiveExtendIsoZeroRow_X f F j).hom :=
  sorry

/-- After extension by zero, the alternating Čech complex of `I^0` identifies with the
zeroth row of `Hom(K^•, I^•)`. -/
noncomputable def alternatingCechInjectiveExtendIsoZeroRow {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F] :
    (alternatingCechComplex f
        ((chosenInjectiveResolution F).cocomplex.X 0)).extend embeddingUpNat ≅
      (homBicomplex f F).zeroRow :=
  HomologicalComplex.Hom.isoOfComponents
    (alternatingCechInjectiveExtendIsoZeroRow_X f F)
    (alternatingCechInjectiveExtendIsoZeroRow_comm f F)

/-- The extended cochain map from the alternating Čech complex to the zeroth row of
`Hom(K^•, I^•)`. -/
noncomputable def alternatingCechToZeroRow {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F] :
    (alternatingCechComplex f F).extend embeddingUpNat ⟶ (homBicomplex f F).zeroRow :=
  HomologicalComplex.extendMap (alternatingCechToHomI0 f F) embeddingUpNat ≫
    (alternatingCechInjectiveExtendIsoZeroRow f F).hom

/-- Components of `alternatingCechToZeroRow` land in vertical cycles of the Hom bicomplex. -/
theorem alternatingCechToZeroRow_cycles {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F]
    (p : ℤ) :
    (alternatingCechToZeroRow f F).f p ≫ ((homBicomplex f F).X p).d 0 1 = 0 :=
  sorry

/-- The comparison `Čech_alt(f, F) ⟶ Tot(Hom(K^•, I^•))` from the zeroth row. -/
noncomputable def alternatingCechToTotal {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F] :
    (alternatingCechComplex f F).extend embeddingUpNat ⟶
      (homBicomplex f F).total (up ℤ) :=
  ZeroRow.ToTotal.map (alternatingCechToZeroRow f F) (alternatingCechToZeroRow_cycles f F)

/-- Global sections of the extended injective resolution. -/
noncomputable def injectiveGammaComplex {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F] :
    CochainComplex AddCommGrpCat.{u + 1} ℤ :=
  ((globalSections X).mapHomologicalComplex (up ℤ)).obj (injectiveCocomplexExtend F)

/-- Opposite of the truncated Koszul augmentation, as a morphism `op ℤ̲ ⟶ K^0` after
extension by zero. -/
noncomputable def koszulAugmentationOp {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f] :
    op (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology X)) ⟶ (koszulComplexExtend f).X 0 :=
  (traceKoszulToConstantComponent f).op ≫
    (extendXIso (HomologicalComplex.op (koszulComplex f)) embeddingUpNat
      (by rfl)).inv

/-- Degreewise components of `Γ(X, I^•) ⟶ Hom(K^0, I^•)`. -/
noncomputable def injectiveGammaToZeroColumn_f {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F]
    (q : ℤ) :
    (injectiveGammaComplex F).X q ⟶ ((homBicomplex f F).zeroColumn).X q :=
  (preadditiveYoneda.flip.map (koszulAugmentationOp f)).app
    ((injectiveCocomplexExtend F).X q)

/-- The degreewise augmentation maps commute with differentials. -/
theorem injectiveGammaToZeroColumn_comm {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F]
    (i j : ℤ) (hij : (up ℤ).Rel i j) :
    injectiveGammaToZeroColumn_f f F i ≫ ((homBicomplex f F).zeroColumn).d i j =
      (injectiveGammaComplex F).d i j ≫ injectiveGammaToZeroColumn_f f F j :=
  sorry

/-- The cochain map `Γ(X, I^•) ⟶ Hom(K^0, I^•)` induced by the truncated Koszul
augmentation. -/
noncomputable def injectiveGammaToZeroColumn {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F] :
    injectiveGammaComplex F ⟶ (homBicomplex f F).zeroColumn where
  f := injectiveGammaToZeroColumn_f f F
  comm' := injectiveGammaToZeroColumn_comm f F

/-- Components of `injectiveGammaToZeroColumn` land in horizontal cycles of the Hom bicomplex. -/
theorem injectiveGammaToZeroColumn_cycles {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F]
    (q : ℤ) :
    (injectiveGammaToZeroColumn f F).f q ≫ ((homBicomplex f F).d 0 1).f q = 0 :=
  sorry

/-- The comparison `Γ(X, I^•) ⟶ Tot(Hom(K^•, I^•))` from the zeroth column. -/
noncomputable def injectiveGammaToTotal {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F] :
    injectiveGammaComplex F ⟶ (homBicomplex f F).total (up ℤ) :=
  ZeroColumn.ToTotal.map (injectiveGammaToZeroColumn f F)
    (injectiveGammaToZeroColumn_cycles f F)

/-- Because `K^•` resolves `ℤ̲`, the comparison `Γ(X, I^•) ⟶ Tot(Hom(K^•, I^•))` is a
quasi-isomorphism. -/
instance injectiveGammaToTotal_quasiIso {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F] :
    QuasiIso (injectiveGammaToTotal f F) :=
  sorry

/-- The extended injective resolution, as a cochain map from `F` concentrated in degree zero. -/
noncomputable def injectiveResolution_ι_extend {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F] :
    ((CochainComplex.single₀
        (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})).obj F).extend embeddingUpNat ⟶
      injectiveCocomplexExtend F :=
  HomologicalComplex.extendMap (chosenInjectiveResolution F).ι embeddingUpNat

/-- Extending the degree-zero complex of `F` recovers the single complex in degree zero on `ℤ`. -/
noncomputable def singleZeroExtendIso {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})] :
    ((CochainComplex.single₀
        (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})).obj F).extend embeddingUpNat ≅
      (HomologicalComplex.single
        (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (up ℤ) 0).obj F :=
  HomologicalComplex.extendSingleIso embeddingUpNat F 0 0 rfl

/-- The comparison `F[0] ⟶ I^•` in unbounded cochain complexes. -/
noncomputable def singleToInjectiveCocomplexExtend {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F] :
    (HomologicalComplex.single
        (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (up ℤ) 0).obj F ⟶
      injectiveCocomplexExtend F :=
  (singleZeroExtendIso F).inv ≫ injectiveResolution_ι_extend F

/-- The comparison `F[0] ⟶ I^•` is a quasi-isomorphism. -/
instance singleToInjectiveCocomplexExtend_quasiIso {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [CategoryWithHomology (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F] :
    QuasiIso (singleToInjectiveCocomplexExtend F) :=
  sorry

/-- The homology of global sections of the extended injective resolution computes sheaf cohomology. -/
theorem injectiveGammaComplex_homology {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F] (n : ℕ) :
    IsIsomorphic ((injectiveGammaComplex F).homology n)
      ((Sheaf.functorH (smallEtaleTopology X) n).obj F) := sorry

/-- The Hom bicomplex of a surjective étale morphism has the first-filtration graded-piece
comparisons identifying each column with the corresponding signed vertical Hom-complex. -/
theorem homBicomplex_firstGradedPieceComparisons {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F] :
    First.GradedPiece.Comparisons (homBicomplex f F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
