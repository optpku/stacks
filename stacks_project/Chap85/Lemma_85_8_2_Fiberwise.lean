/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Embedding.Connect
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import stacks_project.Chap85.Lemma_85_8_1_Fiberwise

/-!
# Hom cochain complex of `g_{n!} ℤ` on a fiberwise simplicial site

In Situation 85.3.3 case B, applying `Hom(-, G)` to the simplicial resolution
`n ↦ g_{n!} ℤ` on the total Grothendieck construction yields a cosimplicial
abelian group, an unaugmented cochain complex, and the extended ℤ-indexed complex with
`Hom(ℤ, G)` in degree `-1`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable [∀ n, (ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, (ι F (op n)).IsCocontinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, ∀ P : (F.obj n)ᵒᵖ ⥤ Type w, (ι F n).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

/-- The cosimplicial abelian group `n ↦ Hom(g_{n!} ℤ, G)` obtained by applying
`Hom(-, G)` to `fiberLowerShriekConstant`. -/
def fiberHomCosimplicial (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    CosimplicialObject AddCommGrpCat.{max u w} :=
  (fiberLowerShriekConstant F J).rightOp ⋙ preadditiveYoneda.obj G

/-- Degree `n` of `fiberHomCosimplicial` is the Hom group `Hom(g_{n!} ℤ, G)`. -/
theorem fiberHomCosimplicial_obj (G : Sheaf (topology F J) AddCommGrpCat.{w})
    (n : SimplexCategory) :
    (fiberHomCosimplicial F J G).obj n =
      (preadditiveYoneda.obj G).obj (op ((fiberLowerShriekConstant F J).obj (op n))) :=
  sorry

/-- Functoriality of `n ↦ Hom(g_{n!} ℤ, G)` in the abelian sheaf `G`. -/
def fiberHomCosimplicialFunctor :
    Sheaf (topology F J) AddCommGrpCat.{w} ⥤
      CosimplicialObject AddCommGrpCat.{max u w} where
  obj G := fiberHomCosimplicial F J G
  map {G H} φ := whiskerLeft (fiberLowerShriekConstant F J).rightOp (preadditiveYoneda.map φ)
  map_id := sorry
  map_comp := sorry

/-- The unaugmented cochain complex `Hom(g_{0!} ℤ, G) → Hom(g_{1!} ℤ, G) → ⋯`. -/
abbrev fiberSectionsComplex (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    CochainComplex AddCommGrpCat.{max u w} ℕ :=
  (alternatingCofaceMapComplex _).obj (fiberHomCosimplicial F J G)

/-- Degree `n` of `fiberSectionsComplex` is `Hom(g_{n!} ℤ, G)`. -/
theorem fiberSectionsComplex_X (G : Sheaf (topology F J) AddCommGrpCat.{w}) (n : ℕ) :
    (fiberSectionsComplex F J G).X n =
      (preadditiveYoneda.obj G).obj (op ((fiberLowerShriekConstant F J).obj (op ⦋n⦌))) :=
  sorry

/-- Differentials of `fiberSectionsComplex` are alternating sums of cofaces
`Hom(fiberFace i, G)`. -/
theorem fiberSectionsComplex_d_eq (G : Sheaf (topology F J) AddCommGrpCat.{w}) (n : ℕ) :
    (fiberSectionsComplex F J G).d n (n + 1) =
      ∑ i : Fin (n + 2),
        (-1 : ℤ) ^ (i : ℕ) • (preadditiveYoneda.obj G).map (fiberFace F J n i).op :=
  sorry

/-- The Hom group `Hom(ℤ, G)` of morphisms from the constant integer sheaf on
the total fiberwise site. -/
def fiberSectionsTotal (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    AddCommGrpCat.{max u w} :=
  (preadditiveYoneda.obj G).obj (op (constantIntegerSheaf (topology F J)))

/-- `fiberSectionsTotal` is the preadditive Yoneda value at the constant sheaf `ℤ`. -/
theorem fiberSectionsTotal_eq (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    fiberSectionsTotal F J G =
      (preadditiveYoneda.obj G).obj (op (constantIntegerSheaf (topology F J))) :=
  sorry

/-- The Hom group `Hom(g_{n!} ℤ, G)` in degree `n`. -/
def fiberSectionsStage (G : Sheaf (topology F J) AddCommGrpCat.{w})
    (n : SimplexCategory) : AddCommGrpCat.{max u w} :=
  (fiberHomCosimplicial F J G).obj n

/-- `fiberSectionsStage` recovers the corresponding object of `fiberHomCosimplicial`. -/
theorem fiberSectionsStage_eq (G : Sheaf (topology F J) AddCommGrpCat.{w})
    (n : SimplexCategory) :
    fiberSectionsStage F J G n =
      (preadditiveYoneda.obj G).obj (op ((fiberLowerShriekConstant F J).obj (op n))) :=
  sorry

/-- Adjunction identification `Hom(g_{n!} ℤ, G) ≃ Hom(ℤ_n, G_n)`. -/
def fiberSectionsStage_addEquivRestrict (G : Sheaf (topology F J) AddCommGrpCat.{w})
    (n : SimplexCategory) :
    ((fiberLowerShriekConstant F J).obj (op n) ⟶ G) ≃+
      (fiberConstantInteger F J n ⟶ (fiberRestrict F J AddCommGrpCat.{w} n).obj G) where
  toEquiv :=
    (fiberAbelianLowerShriek_adjunction F J n).homEquiv (fiberConstantInteger F J n) G
  map_add' := sorry

/-- Global sections of `G` identify additively with morphisms `ℤ ⟶ G`. -/
def fiberSectionsTotal_addEquivGamma
    [HasGlobalSectionsFunctor (topology F J) AddCommGrpCat.{w}]
    (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    (Sheaf.Γ (topology F J) AddCommGrpCat.{w}).obj G ≃+
      (constantIntegerSheaf (topology F J) ⟶ G) :=
  Sheaf.globalSectionsAddEquivConstantIntegerSheafHomOnSite (topology F J) G

/-- Global sections of `G_n` identify additively with morphisms `ℤ_n ⟶ G_n`. -/
def fiberSectionsStage_addEquivGamma
    (n : SimplexCategory)
    [HasSheafify ((J (op n)).toGrothendieck) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor ((J (op n)).toGrothendieck) AddCommGrpCat.{w}]
    (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    (Sheaf.Γ ((J (op n)).toGrothendieck) AddCommGrpCat.{w}).obj
        ((fiberRestrict F J AddCommGrpCat.{w} n).obj G) ≃+
      (fiberConstantInteger F J n ⟶ (fiberRestrict F J AddCommGrpCat.{w} n).obj G) :=
  Sheaf.globalSectionsAddEquivConstantIntegerSheafHomOnSite ((J (op n)).toGrothendieck)
    ((fiberRestrict F J AddCommGrpCat.{w} n).obj G)

/-- The coaugmentation `Hom(ℤ, G) ⟶ Hom(g_{0!} ℤ, G)`, dual to the degree-zero
component of `fiberAugmentation`. -/
def fiberSectionsCoaugmentation (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    fiberSectionsTotal F J G ⟶ (fiberSectionsComplex F J G).X 0 :=
  (preadditiveYoneda.obj G).map ((fiberAugmentation F J).f 0).op

/-- The coaugmentation is Hom of the simplicial augmentation at `⦋0⦌`. -/
theorem fiberSectionsCoaugmentation_eq (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    fiberSectionsCoaugmentation F J G =
      (preadditiveYoneda.obj G).map ((fiberAugmented F J).hom.app (op ⦋0⦌)).op :=
  sorry

/-- The coaugmentation equalizes the first coface differential. -/
theorem fiberSectionsCoaugmentation_comp_d
    (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    fiberSectionsCoaugmentation F J G ≫ (fiberSectionsComplex F J G).d 0 1 = 0 :=
  sorry

/-- The connecting differential `Hom(ℤ, G) ⟶ Hom(g_{0!} ℤ, G)` from
`single₀ Hom(ℤ, G)` into the unaugmented Hom cochain. -/
def fiberSectionsConnect_d₀ (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    ((ChainComplex.single₀ _).obj (fiberSectionsTotal F J G)).X 0 ⟶
      (fiberSectionsComplex F J G).X 0 :=
  fiberSectionsCoaugmentation F J G

/-- The connecting differential is the coaugmentation `Hom(ℤ, G) ⟶ Hom(g_{0!} ℤ, G)`. -/
theorem fiberSectionsConnect_d₀_eq (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    fiberSectionsConnect_d₀ F J G = fiberSectionsCoaugmentation F J G :=
  sorry

/-- The connecting differential annihilates the outgoing differential of
`single₀ Hom(ℤ, G)`. -/
theorem fiberSectionsConnect_comp_d₀ (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    ((ChainComplex.single₀ _).obj (fiberSectionsTotal F J G)).d 1 0 ≫
      fiberSectionsConnect_d₀ F J G = 0 :=
  sorry

/-- The connecting differential equalizes the first coface of the unaugmented Hom cochain. -/
theorem fiberSectionsConnect_d₀_comp (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    fiberSectionsConnect_d₀ F J G ≫ (fiberSectionsComplex F J G).d 0 1 = 0 :=
  sorry

/-- Connecting data for the ℤ-indexed Hom cochain, with `Hom(ℤ, G)` in degree `-1`. -/
def fiberSectionsConnect (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    CochainComplex.ConnectData
      ((ChainComplex.single₀ _).obj (fiberSectionsTotal F J G))
      (fiberSectionsComplex F J G) where
  d₀ := fiberSectionsConnect_d₀ F J G
  comp_d₀ := fiberSectionsConnect_comp_d₀ F J G
  d₀_comp := fiberSectionsConnect_d₀_comp F J G

/-- The extended cochain complex with `Hom(ℤ, G)` in degree `-1` and
`Hom(g_{n!} ℤ, G)` in degree `n`. -/
def fiberSectionsExtended (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    CochainComplex AddCommGrpCat.{max u w} ℤ :=
  (fiberSectionsConnect F J G).cochainComplex

/-- Degree `-1` of the extended complex is `Hom(ℤ, G)`, equivalently `Γ(C_total, G)`. -/
theorem fiberSectionsExtended_X_negOne (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    (fiberSectionsExtended F J G).X (-1) = fiberSectionsTotal F J G :=
  sorry

/-- Nonnegative degrees of the extended complex recover the unaugmented Hom complex. -/
theorem fiberSectionsExtended_X_ofNat (G : Sheaf (topology F J) AddCommGrpCat.{w})
    (n : ℕ) :
    (fiberSectionsExtended F J G).X n = (fiberSectionsComplex F J G).X n :=
  sorry

/-- The differential out of degree `-1` is the coaugmentation. -/
theorem fiberSectionsExtended_d_negOne_zero
    (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    (fiberSectionsExtended F J G).d (-1) 0 = fiberSectionsConnect_d₀ F J G :=
  sorry

/-- The coaugmentation as a morphism from `Hom(ℤ, G)` concentrated in degree 0
to the unaugmented Hom complex. -/
def fiberSectionsAugmentation (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    (CochainComplex.single₀ _).obj (fiberSectionsTotal F J G) ⟶
      fiberSectionsComplex F J G :=
  (CochainComplex.fromSingle₀Equiv (fiberSectionsComplex F J G)
      (fiberSectionsTotal F J G)).symm
    ⟨fiberSectionsCoaugmentation F J G, fiberSectionsCoaugmentation_comp_d F J G⟩

/-- For injective coefficients, the unaugmented coaugmentation is a quasi-isomorphism. -/
instance fiberSectionsAugmentation_quasiIso
    (G : Sheaf (topology F J) AddCommGrpCat.{w}) [Injective G] :
    QuasiIso (fiberSectionsAugmentation F J G) :=
  sorry

/-- Functoriality of the unaugmented Hom cochain complex in the sheaf variable. -/
def fiberSectionsComplexFunctor :
    Sheaf (topology F J) AddCommGrpCat.{w} ⥤
      CochainComplex AddCommGrpCat.{max u w} ℕ :=
  fiberHomCosimplicialFunctor F J ⋙ alternatingCofaceMapComplex _

end CategoryTheory.Grothendieck
