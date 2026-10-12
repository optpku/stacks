/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Naturality
public import ReasLib.CategoryTheory.Homology.DoubleComplex.CoaugmentedResolution
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Pages
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import stacks_project.Chap85.Lemma_85_8_2_Fiberwise

/-!
# Čech–injective double complex on a fiberwise simplicial site

In Situation 85.3.3 case B, a cochain complex `I` of abelian sheaves on the total
fiberwise site determines the double complex `A^{p,q} = Γ(C_p, I^q_p)` whose
horizontal differentials are those of `fiberSectionsComplex`. The associated
first-page and abutment functors on `DerivedCategory.Plus` recover
`H^q(C_p, K_p)` and `H^n(C_total, K)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex ComplexShape DerivedCategory ZeroObject
open scoped HomologicalComplex₂

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

/-- The Čech cochain functor on abelian sheaves on the total fiberwise site preserves
zero morphisms. -/
instance fiberSectionsComplexFunctor_preservesZeroMorphisms :
    (fiberSectionsComplexFunctor F J).PreservesZeroMorphisms :=
  sorry

/-- The Čech cochain functor on abelian sheaves on the total fiberwise site is additive. -/
instance fiberSectionsComplexFunctor_additive :
    (fiberSectionsComplexFunctor F J).Additive :=
  sorry

/-- The ℕ-indexed cochain of vertical complexes `p ↦ (q ↦ Γ(C_p, I^q_p))`. -/
def fiberSectionsColumnsFunctor :
    CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ ⥤
      CochainComplex (CochainComplex AddCommGrpCat.{max u w} ℤ) ℕ :=
  (fiberSectionsComplexFunctor F J).mapHomologicalComplex (up ℤ) ⋙
    HomologicalComplex₂.flipFunctor _ (up ℤ) (up ℕ)

/-- The Čech–injective double complex functor, reindexed from nonnegative Čech degree. -/
def fiberSectionsBicomplexFunctor :
    CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ ⥤
      HomologicalComplex₂ AddCommGrpCat.{max u w} (up ℤ) (up ℤ) :=
  fiberSectionsColumnsFunctor F J ⋙
    HomologicalComplex₂.CoaugmentedResolution.bicomplexFunctor

/-- The double complex `A^{p,q} = Γ(C_p, I^q_p)` of a cochain complex of abelian sheaves. -/
def fiberSectionsBicomplex
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ) :
    HomologicalComplex₂ AddCommGrpCat.{max u w} (up ℤ) (up ℤ) :=
  (fiberSectionsBicomplexFunctor F J).obj I

/-- Nonnegative columns of `fiberSectionsBicomplex` recover stagewise global sections of `I`. -/
theorem fiberSectionsBicomplex_X_ofNat
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    (p : ℕ) (q : ℤ) :
    ((fiberSectionsBicomplex F J I).X p).X q =
      (fiberSectionsComplex F J (I.X q)).X p :=
  sorry

/-- Negative Čech columns of `fiberSectionsBicomplex` vanish. -/
theorem fiberSectionsBicomplex_isZero_of_neg
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    {p : ℤ} (hp : p < 0) :
    IsZero ((fiberSectionsBicomplex F J I).X p) :=
  sorry

/-- The functor `G ↦ Hom(ℤ, G)`, equivalently `Γ(C_total, G)` after Yoneda. -/
def fiberSectionsTotalFunctor :
    Sheaf (topology F J) AddCommGrpCat.{w} ⥤ AddCommGrpCat.{max u w} :=
  preadditiveYoneda.flip.obj (op (constantIntegerSheaf (topology F J)))

/-- `fiberSectionsTotalFunctor` recovers `fiberSectionsTotal`. -/
theorem fiberSectionsTotalFunctor_obj
    (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    (fiberSectionsTotalFunctor F J).obj G = fiberSectionsTotal F J G :=
  sorry

/-- Global sections of the total fiberwise site, as a Hom functor, preserve zero morphisms. -/
instance fiberSectionsTotalFunctor_preservesZeroMorphisms :
    (fiberSectionsTotalFunctor F J).PreservesZeroMorphisms :=
  sorry

/-- The coaugmentation source `Γ(C_total, I^•)` as a cochain complex. -/
def fiberSectionsTotalComplex
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ) :
    CochainComplex AddCommGrpCat.{max u w} ℤ :=
  ((fiberSectionsTotalFunctor F J).mapHomologicalComplex (up ℤ)).obj I

/-- The coaugmentation `Γ(C_total, I^•) ⟶` the zeroth column of the Čech bicomplex. -/
def fiberSectionsBicomplexCoaugmentation
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ) :
    fiberSectionsTotalComplex F J I ⟶
      ((fiberSectionsColumnsFunctor F J).obj I).X 0 where
  f q := fiberSectionsCoaugmentation F J (I.X q)
  comm' := sorry

/-- The coaugmentation is killed by the first Čech differential. -/
theorem fiberSectionsBicomplexCoaugmentation_comp_d
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ) :
    fiberSectionsBicomplexCoaugmentation F J I ≫
      ((fiberSectionsColumnsFunctor F J).obj I).d 0 1 = 0 :=
  sorry

/-- Degree-`n` functor sending an abelian sheaf on `C_total` to `Γ(C_n, G_n)`. -/
def fiberSectionsStageGamma (n : ℕ) :
    Sheaf (topology F J) AddCommGrpCat.{w} ⥤ AddCommGrpCat.{max u w} :=
  fiberSectionsComplexFunctor F J ⋙
    HomologicalComplex.eval AddCommGrpCat.{max u w} (up ℕ) n

/-- Stagewise global sections are additive. -/
instance fiberSectionsStageGamma_additive (n : ℕ) :
    (fiberSectionsStageGamma F J n).Additive :=
  sorry

/-- The Čech differential as a natural transformation of stagewise global sections. -/
def fiberSectionsStageGamma_d (n : ℕ) :
    fiberSectionsStageGamma F J n ⟶ fiberSectionsStageGamma F J (n + 1) where
  app G := (fiberSectionsComplex F J G).d n (n + 1)
  naturality := sorry

variable [∀ n : ℕ,
    (fiberSectionsStageGamma F J n).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf (topology F J) AddCommGrpCat.{w}))]
variable [(fiberSectionsTotalFunctor F J).Additive]
variable [(fiberSectionsTotalFunctor F J).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf (topology F J) AddCommGrpCat.{w}))]

/-- Nonnegative first-page target: `H^q` of the derived functor of `Γ(C_n, (-)_n)`. -/
def fiberPageOneFunctorNonneg (n : ℕ) (q : ℤ) :
    DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w}) ⥤
      AddCommGrpCat.{max u w} :=
  Functor.RightDerived.Bounded.functor (fiberSectionsStageGamma F J n) ⋙
    DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} q

/-- The Čech differential on nonnegative first-page functors. -/
def fiberPageOneDifferentialNonneg (n : ℕ) (q : ℤ) :
    fiberPageOneFunctorNonneg F J n q ⟶ fiberPageOneFunctorNonneg F J (n + 1) q :=
  whiskerRight
    (Functor.RightDerived.Bounded.map (fiberSectionsStageGamma_d F J n))
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} q)

/-- Successor of a nonnegative integer remains nonnegative. -/
theorem fiber_nonneg_succ {n : ℤ} (hn : 0 ≤ n) : 0 ≤ n + 1 :=
  sorry

/-- `toNat` converts a successor of a nonnegative integer into a successor of naturals. -/
theorem fiber_toNat_succ_of_nonneg {n : ℤ} (hn : 0 ≤ n) :
    (n + 1).toNat = n.toNat + 1 :=
  sorry

/-- First-page target `K ↦ H^q(C_p, K_p)`, vanishing for `p < 0`. -/
def fiberPageOneFunctor (p q : ℤ) :
    DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w}) ⥤
      AddCommGrpCat.{max u w} :=
  if 0 ≤ p then fiberPageOneFunctorNonneg F J p.toNat q else
    (Functor.const
      (DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w}))).obj
      (0 : AddCommGrpCat.{max u w})

/-- Nonnegative bidegrees of `fiberPageOneFunctor` recover `fiberPageOneFunctorNonneg`. -/
theorem fiberPageOneFunctor_eq_of_nonneg (p q : ℤ) (hp : 0 ≤ p) :
    fiberPageOneFunctor F J p q = fiberPageOneFunctorNonneg F J p.toNat q :=
  sorry

/-- The first-page differential `d₁^{p,q} : E₁^{p,q} ⟶ E₁^{p+1,q}`. -/
def fiberPageOneDifferential (p q : ℤ) :
    fiberPageOneFunctor F J p q ⟶ fiberPageOneFunctor F J (p + 1) q :=
  if hp : 0 ≤ p then
    eqToHom (fiberPageOneFunctor_eq_of_nonneg F J p q hp) ≫
      fiberPageOneDifferentialNonneg F J p.toNat q ≫
      eqToHom (congrArg (fiberPageOneFunctorNonneg F J · q)
        (fiber_toNat_succ_of_nonneg hp)).symm ≫
      eqToHom (fiberPageOneFunctor_eq_of_nonneg F J (p + 1) q
        (fiber_nonneg_succ hp)).symm
  else
    (0 : fiberPageOneFunctor F J p q ⟶ fiberPageOneFunctor F J (p + 1) q)

/-- First-page groups in negative Čech degree vanish. -/
theorem fiberPageOneFunctor_neg
    (K : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w}))
    {p : ℤ} (hp : p < 0) (q : ℤ) :
    IsZero ((fiberPageOneFunctor F J p q).obj K) :=
  sorry

/-- Abutment functor `K ↦ H^n(C_total, K)`. -/
def fiberAbutmentFunctor (n : ℤ) :
    DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w}) ⥤
      AddCommGrpCat.{max u w} :=
  Functor.RightDerived.Bounded.functor (fiberSectionsTotalFunctor F J) ⋙
    DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} n

/-- Evaluation of `fiberAbutmentFunctor` is cohomology of `RΓ(C_total, -)`. -/
theorem fiberAbutmentFunctor_obj
    (n : ℤ)
    (K : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w})) :
    (fiberAbutmentFunctor F J n).obj K =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} n).obj
        ((Functor.RightDerived.Bounded.functor
          (fiberSectionsTotalFunctor F J)).obj K) :=
  sorry

/-- For a bounded-below complex of injectives representing `K`, vertical homology of
`fiberSectionsBicomplex` recovers the first-page target. -/
theorem fiberPageOne_isomorphic_of_injectiveRepresentative
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    (hI : CochainComplex.plus _ I) [∀ n, Injective (I.X n)]
    (K : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w}))
    (hK : Nonempty
      (DerivedCategory.Plus.ι.obj K ≅ DerivedCategory.Q.obj I))
    (p q : ℤ) :
    IsIsomorphic
      (HomologicalComplex₂.First.PageOne.entry (fiberSectionsBicomplex F J I) p q)
      ((fiberPageOneFunctor F J p q).obj K) :=
  sorry

/-- The coaugmentation-to-total comparison is a quasi-isomorphism when every term of `I`
is injective. -/
theorem fiberSectionsToTotal_quasiIso
    [HasCountableCoproducts AddCommGrpCat.{max u w}]
    [CountableAB4 AddCommGrpCat.{max u w}]
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    [∀ n, Injective (I.X n)] :
    QuasiIso
      (HomologicalComplex₂.CoaugmentedResolution.ToTotal.map
        ((fiberSectionsColumnsFunctor F J).obj I)
        (fiberSectionsBicomplexCoaugmentation F J I)
        (fiberSectionsBicomplexCoaugmentation_comp_d F J I)) :=
  sorry

end CategoryTheory.Grothendieck
