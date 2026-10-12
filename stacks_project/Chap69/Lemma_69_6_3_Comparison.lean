/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import ReasLib.CategoryTheory.Homology.DoubleComplex.TotalComparison
public import stacks_project.Chap69.«69_6_1_1_Koszul»
public import stacks_project.Chap69.Definition_69_6_2
public import stacks_project.Chap69.Lemma_69_6_3_DerivedSections

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

/-- The embedding `ℕ ↪ ℤ` is the canonical coercion on objects. -/
theorem embeddingUpNat_f_nat (n : ℕ) : embeddingUpNat.f n = n :=
  rfl

/-- Degrees of the embedding `ℕ ↪ ℤ` are the corresponding nonnegative integers. -/
theorem embeddingUpNat_f_toNat {n : ℤ} (hn : 0 ≤ n) :
    embeddingUpNat.f n.toNat = n :=
  Int.toNat_of_nonneg hn

/-- Negative integers are not in the image of `embeddingUpNat`. -/
theorem embeddingUpNat_not_eq_of_not_nonneg {n : ℤ} (hn : ¬ 0 ≤ n) (i : ℕ) :
    embeddingUpNat.f i ≠ n :=
  sorry

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
    [hF : HasInjectiveResolution F] :
    InjectiveResolution F :=
  hF.out.some

/-- An injective resolution of `F`, extended by zero from `ℕ` to `ℤ`. -/
noncomputable def injectiveCocomplexExtend {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
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
        (embeddingUpNat_f_nat p))).app
    ((injectiveCocomplexExtend F).X q) ≪≫
  (preadditiveYoneda.flip.obj (op ((koszulComplex f).X p))).mapIso
    (extendXIso (chosenInjectiveResolution F).cocomplex embeddingUpNat
      (embeddingUpNat_f_nat q))

/-- The Hom bicomplex of a first-quadrant Hom-diagram admits a total complex. -/
instance homBicomplex_hasTotal {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F] :
    (homBicomplex f F).HasTotal (up ℤ) :=
  sorry

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
        embeddingUpNat (embeddingUpNat_f_toNat hn) ≪≫
      (preadditiveYoneda.flip.obj (op ((koszulComplex f).X n.toNat))).mapIso
        (extendXIso (chosenInjectiveResolution F).cocomplex embeddingUpNat
          (embeddingUpNat_f_nat 0)).symm ≪≫
      (preadditiveYoneda.flip.mapIso
        (extendXIso (HomologicalComplex.op (koszulComplex f)) embeddingUpNat
          (embeddingUpNat_f_toNat hn)).symm).app
        ((injectiveCocomplexExtend F).X 0)
  else
    IsZero.iso
      (isZero_alternatingCechComplex_extend_of_not_nonneg f
        ((chosenInjectiveResolution F).cocomplex.X 0) n hn)
      (isZero_homBicomplex_zeroRow_of_not_nonneg f F n hn)

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
    op (constantIntegerSheaf X) ⟶ (koszulComplexExtend f).X 0 :=
  (traceKoszulToConstantComponent f).op ≫
    (extendXIso (HomologicalComplex.op (koszulComplex f)) embeddingUpNat
      (embeddingUpNat_f_nat 0)).inv

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

/-- Localization of the quasi-isomorphism `Γ(X, I^•) ⟶ Tot` is an isomorphism in `D(Ab)`. -/
instance isIso_Q_map_injectiveGammaToTotal {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F]
    [HasDerivedCategory AddCommGrpCat.{u + 1}] :
    IsIso (DerivedCategory.Q.map (injectiveGammaToTotal f F)) :=
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

end AlgebraicGeometry.AlgebraicSpace
