module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Sites.Abelian
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Integer
public import stacks_project.Chap85.Lemma_85_3_5_Fiber

/-!
# Alternating-face complex of `g_{n!} ℤ` on a fiberwise simplicial site

In Situation 85.3.3 case B, the simplicial abelian sheaf `n ↦ g_{n!} ℤ` on the
total Grothendieck construction, its augmentation to the constant sheaf `ℤ`,
and the associated alternating-face chain complex.
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
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

/-- The constant sheaf with value `ULift ℤ` on the degree-`n` fiber. -/
abbrev fiberConstantInteger (n : SimplexCategory) :
    Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w} :=
  constantIntegerSheaf (J (op n)).toGrothendieck

/-- Unfolding `fiberConstantInteger` recovers `constantIntegerSheaf` on the fiber topology. -/
theorem fiberConstantInteger_eq (n : SimplexCategory) :
    fiberConstantInteger F J n = constantIntegerSheaf (J (op n)).toGrothendieck :=
  sorry

/-- Identification of the pullback of a constant integer presheaf along `u_φ` with
the constant integer sheaf on the target fiber. -/
def fiberFace_constCompIso {n m : SimplexCategory} (φ : n ⟶ m) :
    (presheafToSheaf ((J (op m)).toGrothendieck) AddCommGrpCat.{w}).obj
      ((F.map φ.op).toFunctor.op ⋙
        ((Functor.const ((F.obj (op n))ᵒᵖ)).obj (AddCommGrpCat.of (ULift.{w} ℤ)))) ≅
    fiberConstantInteger F J m where
  hom := (presheafToSheaf ((J (op m)).toGrothendieck) AddCommGrpCat.{w}).map
    ((constCompWhiskeringLeftIso (F.obj (op m))ᵒᵖ (F.map φ.op).toFunctor.op).hom.app
      (AddCommGrpCat.of (ULift.{w} ℤ)))
  inv := (presheafToSheaf ((J (op m)).toGrothendieck) AddCommGrpCat.{w}).map
    ((constCompWhiskeringLeftIso (F.obj (op m))ᵒᵖ (F.map φ.op).toFunctor.op).inv.app
      (AddCommGrpCat.of (ULift.{w} ℤ)))
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Sheafification of the unit identifies the pulled-back constant presheaf with
`f_φ⁻¹ ℤ_n`. -/
def fiberFace_unitWhisker {n m : SimplexCategory} (φ : n ⟶ m) :
    (presheafToSheaf ((J (op m)).toGrothendieck) AddCommGrpCat.{w}).obj
      ((F.map φ.op).toFunctor.op ⋙
        ((Functor.const ((F.obj (op n))ᵒᵖ)).obj (AddCommGrpCat.of (ULift.{w} ℤ)))) ⟶
    ((F.map φ.op).toFunctor.sheafPullbackCocontinuous AddCommGrpCat.{w}
      (J (op m)).toGrothendieck (J (op n)).toGrothendieck).obj
      (fiberConstantInteger F J n) :=
  (presheafToSheaf ((J (op m)).toGrothendieck) AddCommGrpCat.{w}).map
    (whiskerLeft (F.map φ.op).toFunctor.op
      ((sheafificationAdjunction (J (op n)).toGrothendieck AddCommGrpCat.{w}).unit.app
        ((Functor.const ((F.obj (op n))ᵒᵖ)).obj (AddCommGrpCat.of (ULift.{w} ℤ)))))

/-- The comparison from the pulled-back constant integer presheaf to `ℤ_m`. -/
def fiberFacePullback_constantInteger_hom {n m : SimplexCategory} (φ : n ⟶ m) :
    (presheafToSheaf ((J (op m)).toGrothendieck) AddCommGrpCat.{w}).obj
      ((F.map φ.op).toFunctor.op ⋙
        ((Functor.const ((F.obj (op n))ᵒᵖ)).obj (AddCommGrpCat.of (ULift.{w} ℤ)))) ⟶
    fiberConstantInteger F J m :=
  (fiberFace_constCompIso F J φ).hom

/-- The comparison `ℤ_m ⟶ f_φ⁻¹ ℤ_n` of constant integer sheaves along a fiberwise
simplex operator. -/
def fiberFacePullback_constantInteger_inv {n m : SimplexCategory} (φ : n ⟶ m) :
    fiberConstantInteger F J m ⟶
      ((F.map φ.op).toFunctor.sheafPullbackCocontinuous AddCommGrpCat.{w}
        (J (op m)).toGrothendieck (J (op n)).toGrothendieck).obj
        (fiberConstantInteger F J n) :=
  (fiberFace_constCompIso F J φ).inv ≫ fiberFace_unitWhisker F J φ

/-- The comparison of pulled-back constant integer sheaves along a fiberwise simplex
operator. -/
def fiberFacePullback_constantIntegerIso {n m : SimplexCategory} (φ : n ⟶ m) :
    (presheafToSheaf ((J (op m)).toGrothendieck) AddCommGrpCat.{w}).obj
      ((F.map φ.op).toFunctor.op ⋙
        ((Functor.const ((F.obj (op n))ᵒᵖ)).obj (AddCommGrpCat.of (ULift.{w} ℤ)))) ≅
    fiberConstantInteger F J m :=
  fiberFace_constCompIso F J φ

/-- The forward comparison of `fiberFacePullback_constantIntegerIso` is
`fiberFacePullback_constantInteger_hom`. -/
theorem fiberFacePullback_constantIntegerIso_hom_eq {n m : SimplexCategory} (φ : n ⟶ m) :
    (fiberFacePullback_constantIntegerIso F J φ).hom =
      fiberFacePullback_constantInteger_hom F J φ :=
  sorry

/-- The reverse comparison of `fiberFacePullback_constantIntegerIso` is
`fiberFace_constCompIso.inv`. -/
theorem fiberFacePullback_constantIntegerIso_inv_eq {n m : SimplexCategory} (φ : n ⟶ m) :
    (fiberFacePullback_constantIntegerIso F J φ).inv =
      (fiberFace_constCompIso F J φ).inv :=
  sorry

/-- The comparison `ℤ_n ⟶ g_n⁻¹ ℤ` of constant integer sheaves along `ι F (op n)`. -/
def fiberInclusion_constantInteger_hom (n : SimplexCategory) :
    fiberConstantInteger F J n ⟶
      (fiberRestrict F J AddCommGrpCat.{w} n).obj
        (constantIntegerSheaf (topology F J)) :=
  ((sheafificationAdjunction (J (op n)).toGrothendieck AddCommGrpCat.{w}).homEquiv
      ((Functor.const _).obj (AddCommGrpCat.of (ULift.{w} ℤ)))
      ((fiberRestrict F J AddCommGrpCat.{w} n).obj
        (constantIntegerSheaf (topology F J)))).symm
    ((constCompWhiskeringLeftIso (F.obj (op n))ᵒᵖ (ι F (op n)).op).inv.app
      (AddCommGrpCat.of (ULift.{w} ℤ)) ≫
      whiskerLeft (ι F (op n)).op
        ((sheafificationAdjunction (topology F J) AddCommGrpCat.{w}).unit.app
          ((Functor.const _).obj (AddCommGrpCat.of (ULift.{w} ℤ)))))

/-- The structure map `g_{m!} ℤ ⟶ g_{n!} ℤ` induced by a fiberwise simplex operator. -/
def fiberLowerShriekConstant_map {n m : SimplexCategory} (φ : n ⟶ m) :
    (fiberAbelianLowerShriek F J m).obj (fiberConstantInteger F J m) ⟶
      (fiberAbelianLowerShriek F J n).obj (fiberConstantInteger F J n) :=
  ((fiberAbelianLowerShriek_adjunction F J m).homEquiv
      (fiberConstantInteger F J m)
      ((fiberAbelianLowerShriek F J n).obj (fiberConstantInteger F J n))).symm
    ((fiberFacePullback_constantInteger_inv F J φ) ≫
      fiberAbelianLowerShriek_component F J φ (fiberConstantInteger F J n))

/-- Identity simplex operators induce identity structure maps in case B. -/
theorem fiberLowerShriekConstant_map_id (n : SimplexCategory) :
    fiberLowerShriekConstant_map F J (𝟙 n) =
      𝟙 ((fiberAbelianLowerShriek F J n).obj (fiberConstantInteger F J n)) :=
  sorry

/-- Structure maps of `n ↦ g_{n!} ℤ` are functorial in fiberwise simplex operators. -/
theorem fiberLowerShriekConstant_map_comp {l n m : SimplexCategory}
    (ψ : l ⟶ n) (φ : n ⟶ m) :
    fiberLowerShriekConstant_map F J (ψ ≫ φ) =
      fiberLowerShriekConstant_map F J φ ≫ fiberLowerShriekConstant_map F J ψ :=
  sorry

/-- Opposite identity operators act as identity maps in case B. -/
theorem fiberLowerShriekConstant_map_id_op (n : SimplexCategoryᵒᵖ) :
    fiberLowerShriekConstant_map F J (𝟙 n.unop) =
      𝟙 ((fiberAbelianLowerShriek F J n.unop).obj (fiberConstantInteger F J n.unop)) :=
  sorry

/-- Opposite composition of simplex operators acts as composition of structure maps
in case B. -/
theorem fiberLowerShriekConstant_map_comp_op {n m p : SimplexCategoryᵒᵖ}
    (f : n ⟶ m) (g : m ⟶ p) :
    fiberLowerShriekConstant_map F J (f ≫ g).unop =
      fiberLowerShriekConstant_map F J f.unop ≫ fiberLowerShriekConstant_map F J g.unop :=
  sorry

/-- The simplicial abelian sheaf `n ↦ g_{n!} ℤ` on the total fiberwise site. -/
def fiberLowerShriekConstant :
    SimplicialObject (Sheaf (topology F J) AddCommGrpCat.{w}) where
  obj n := (fiberAbelianLowerShriek F J n.unop).obj (fiberConstantInteger F J n.unop)
  map f := fiberLowerShriekConstant_map F J f.unop
  map_id := fiberLowerShriekConstant_map_id_op F J
  map_comp := fiberLowerShriekConstant_map_comp_op F J

/-- The value of `fiberLowerShriekConstant` at `n` is `g_{n!} ℤ`. -/
theorem fiberLowerShriekConstant_obj (n : SimplexCategory) :
    (fiberLowerShriekConstant F J).obj (op n) =
      (fiberAbelianLowerShriek F J n).obj (fiberConstantInteger F J n) :=
  sorry

/-- The source face map `d_i : g_{(n+1)!} ℤ ⟶ g_{n!} ℤ` in case B. -/
def fiberFace (n : ℕ) (i : Fin (n + 2)) :
    (fiberLowerShriekConstant F J).obj (op ⦋n + 1⦌) ⟶
      (fiberLowerShriekConstant F J).obj (op ⦋n⦌) :=
  (fiberLowerShriekConstant F J).δ i

/-- The face map `fiberFace i` is the simplicial operator `δ i`. -/
theorem fiberFace_eq (n : ℕ) (i : Fin (n + 2)) :
    fiberFace F J n i = (fiberLowerShriekConstant F J).δ i :=
  sorry

/-- The component of the case B augmentation `g_{n!} ℤ ⟶ ℤ` at a simplex `n`. -/
def fiberAugmented_hom_app (n : SimplexCategoryᵒᵖ) :
    (fiberLowerShriekConstant F J).obj n ⟶ constantIntegerSheaf (topology F J) :=
  ((fiberAbelianLowerShriek_adjunction F J n.unop).homEquiv
      (fiberConstantInteger F J n.unop) (constantIntegerSheaf (topology F J))).symm
    (fiberInclusion_constantInteger_hom F J n.unop)

/-- Naturality of the degreewise case B augmentation `g_{n!} ℤ ⟶ ℤ`. -/
theorem fiberAugmented_hom_naturality :
    ∀ ⦃n m : SimplexCategoryᵒᵖ⦄ (f : n ⟶ m),
      (fiberLowerShriekConstant F J).map f ≫ fiberAugmented_hom_app F J m =
        fiberAugmented_hom_app F J n ≫
          ((SimplicialObject.const _).obj
            (constantIntegerSheaf (topology F J))).map f :=
  sorry

/-- The natural transformation `n ↦ g_{n!} ℤ ⟶ const ℤ` in case B. -/
def fiberAugmented_hom :
    fiberLowerShriekConstant F J ⟶
      (SimplicialObject.const _).obj (constantIntegerSheaf (topology F J)) where
  app := fiberAugmented_hom_app F J
  naturality := fiberAugmented_hom_naturality F J

/-- The augmented simplicial object of `g_{n!} ℤ` over the constant sheaf `ℤ` in case B. -/
def fiberAugmented :
    SimplicialObject.Augmented (Sheaf (topology F J) AddCommGrpCat.{w}) where
  left := fiberLowerShriekConstant F J
  right := constantIntegerSheaf (topology F J)
  hom := fiberAugmented_hom F J

variable [HasSheafify (topology F J) AddCommGrpCat.{w}]

/-- The alternating-face chain complex `… → g_{2!} ℤ → g_{1!} ℤ → g_{0!} ℤ` in case B. -/
abbrev fiberComplex : ChainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℕ :=
  (alternatingFaceMapComplex _).obj
    (SimplicialObject.Augmented.drop.obj (fiberAugmented F J))

/-- Degree `n` of `fiberComplex F J` is the abelian sheaf `g_{n!} ℤ`. -/
theorem fiberComplex_X (n : ℕ) :
    (fiberComplex F J).X n =
      (fiberAbelianLowerShriek F J ⦋n⦌).obj (fiberConstantInteger F J ⦋n⦌) :=
  sorry

/-- Differentials of `fiberComplex F J` are the alternating sums of face maps. -/
theorem fiberComplex_d_eq (n : ℕ) :
    (fiberComplex F J).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • fiberFace F J n i :=
  sorry

/-- The canonical chain-map augmentation from `fiberComplex F J` to the constant sheaf `ℤ`
concentrated in degree zero. -/
def fiberAugmentation :
    fiberComplex F J ⟶
      (ChainComplex.single₀ _).obj (constantIntegerSheaf (topology F J)) :=
  AlternatingFaceMapComplex.ε.app (fiberAugmented F J)

/-- The degree-zero component of `fiberAugmentation F J` is the simplicial augmentation
at `⦋0⦌`. -/
theorem fiberAugmentation_f_zero :
    (fiberAugmentation F J).f 0 = (fiberAugmented F J).hom.app (op ⦋0⦌) :=
  sorry

end CategoryTheory.Grothendieck
