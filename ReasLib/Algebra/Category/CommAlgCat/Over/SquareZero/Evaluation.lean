/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Products
public import ReasLib.Algebra.Category.ModuleCat.LinearLift
public import ReasLib.Algebra.Category.CommAlgCat.Over.SquareZero.FinitelyGenerated

/-!
# Evaluation of a functor on finitely generated square-zero extensions

The composite `L(M) = F(R[M])`, the induced maps on fibre products of
`R[M]`, and the finite-product hypotheses that produce an `R`-module
structure on each `F(R[M])`.
-/

@[expose] public section

noncomputable section

open CategoryTheory hiding Linear
open CategoryTheory.Limits ZeroObject
open TrivSqZeroExt

universe u

namespace CategoryTheory.Functor

variable {S R : Type u} [CommRing S] [CommRing R] [Algebra S R]
variable {P : ObjectProperty (Over (CommAlgCat.of S R))}

/-- The composite `Mod^{fg}_R ⥤ Type` sending `M` to `F(R[M])`. -/
def fgEval (P : ObjectProperty (Over (CommAlgCat.of S R))) [P.ContainsFGTrivSqZeroExt]
    (F : P.FullSubcategory ⥤ Type u) :
    FGModuleCat.{u} R ⥤ Type u :=
  fgLift P ⋙ F

/-- Evaluation of `fgEval` at `M` is `F(R[M])`. -/
theorem fgEval_obj (P : ObjectProperty (Over (CommAlgCat.of S R))) [P.ContainsFGTrivSqZeroExt]
    (F : P.FullSubcategory ⥤ Type u)
    (M : FGModuleCat.{u} R) :
    (fgEval P F).obj M = F.obj ((fgLift P).obj M) := rfl

/-- `fgEval` acts on morphisms by the underlying action of `F`. -/
theorem fgEval_map (P : ObjectProperty (Over (CommAlgCat.of S R))) [P.ContainsFGTrivSqZeroExt]
    (F : P.FullSubcategory ⥤ Type u)
    {M N : FGModuleCat.{u} R} (f : M ⟶ N) :
    (fgEval P F).map f = F.map ((fgLift P).map f) := rfl

/-- The comparison `F(R[M × N]) ⟶ F(R[M]) × F(R[N])` obtained from the
categorical product in `Mod^{fg}_R`. -/
def fgProdMap (P : ObjectProperty (Over (CommAlgCat.of S R))) [P.ContainsFGTrivSqZeroExt]
    (F : P.FullSubcategory ⥤ Type u)
    (M N : FGModuleCat.{u} R) :
    (fgEval P F).obj (M ⨯ N) → (fgEval P F).obj M × (fgEval P F).obj N :=
  prodComparison (fgEval P F) M N ≫
    (Types.binaryProductIso ((fgEval P F).obj M) ((fgEval P F).obj N)).hom

/-- `fgProdMap` is the product comparison of `fgEval` followed by the
identification of the categorical product of types with the cartesian product. -/
theorem fgProdMap_spec (P : ObjectProperty (Over (CommAlgCat.of S R))) [P.ContainsFGTrivSqZeroExt]
    (F : P.FullSubcategory ⥤ Type u)
    (M N : FGModuleCat.{u} R) :
    fgProdMap P F M N =
      prodComparison (fgEval P F) M N ≫
        (Types.binaryProductIso ((fgEval P F).obj M) ((fgEval P F).obj N)).hom :=
  rfl

/-- The fibre product `R[M] ×_R R[N]` as an object of a strictly full subcategory
containing every `R[M]`. -/
def fgAmbientProdObj (P : ObjectProperty (Over (CommAlgCat.of S R)))
    [P.IsClosedUnderIsomorphisms] [P.ContainsFGTrivSqZeroExt]
    (M N : FGModuleCat.{u} R) : P.FullSubcategory where
  obj := (fgOverFunctor S R).obj M ⨯ (fgOverFunctor S R).obj N
  property := P.prop_of_isIso (prodComparison (fgOverFunctor S R) M N)
    (P.prop_of_is ((fgOverFunctor S R).obj (M ⨯ N)))

/-- The induced map `F(R[M] ×_R R[N]) ⟶ F(R[M]) × F(R[N])`. -/
def fgAmbientProdMap (P : ObjectProperty (Over (CommAlgCat.of S R)))
    [P.IsClosedUnderIsomorphisms] [P.ContainsFGTrivSqZeroExt]
    (F : P.FullSubcategory ⥤ Type u) (M N : FGModuleCat.{u} R) :
    F.obj (fgAmbientProdObj P M N) →
      F.obj ((fgLift P).obj M) × F.obj ((fgLift P).obj N) :=
  fun x ↦ (F.map (ObjectProperty.homMk prod.fst) x, F.map (ObjectProperty.homMk prod.snd) x)

/-- A functor `C ⥤ Type` sends fibre products of finitely generated square-zero
extensions to cartesian products of values. -/
@[mk_iff]
class BijectiveOnFGSquareZeroProds [P.ContainsFGTrivSqZeroExt]
    (F : P.FullSubcategory ⥤ Type u) : Prop where
  /-- The comparison `F(R[M × N]) ⟶ F(R[M]) × F(R[N])` is bijective. -/
  bijective_prod :
    ∀ M N : FGModuleCat.{u} R, Function.Bijective (fgProdMap P F M N)

/-- The constant singleton functor sends fibre products of `R[M]` bijectively to
products of values. -/
instance instBijectiveOnFGSquareZeroProds_constPUnit [P.ContainsFGTrivSqZeroExt] :
    ((const P.FullSubcategory).obj (PUnit : Type u)).BijectiveOnFGSquareZeroProds where
  bijective_prod _ _ :=
    ⟨fun _ _ _ ↦ Subsingleton.elim (α := PUnit) _ _,
      fun _ ↦ ⟨PUnit.unit, Prod.ext (Subsingleton.elim (α := PUnit) _ _)
        (Subsingleton.elim (α := PUnit) _ _)⟩⟩

/-- Bijectivity of the ambient fibre-product map is equivalent to bijectivity of
`fgProdMap`. -/
theorem fgAmbientProdMap_bijective_iff (P : ObjectProperty (Over (CommAlgCat.of S R)))
    [P.IsClosedUnderIsomorphisms]
    [P.ContainsFGTrivSqZeroExt] (F : P.FullSubcategory ⥤ Type u)
    (M N : FGModuleCat.{u} R) :
    Function.Bijective (fgAmbientProdMap P F M N) ↔
      Function.Bijective (fgProdMap P F M N) := by
  let c : (fgLift P).obj (M ⨯ N) ⟶ fgAmbientProdObj P M N :=
    ObjectProperty.homMk (prodComparison (fgOverFunctor S R) M N)
  haveI : IsIso c := (ObjectProperty.isIso_hom_iff c).mp (by
    change IsIso (prodComparison (fgOverFunctor S R) M N)
    infer_instance)
  have hc₁ : c ≫ ObjectProperty.homMk prod.fst = (fgLift P).map prod.fst := by
    apply ObjectProperty.hom_ext
    exact prodComparison_fst (fgOverFunctor S R) M N
  have hc₂ : c ≫ ObjectProperty.homMk prod.snd = (fgLift P).map prod.snd := by
    apply ObjectProperty.hom_ext
    exact prodComparison_snd (fgOverFunctor S R) M N
  have hfst :
      TypeCat.ofHom (fgProdMap P F M N) ≫ TypeCat.ofHom _root_.Prod.fst =
        F.map c ≫ F.map (ObjectProperty.homMk prod.fst) := by
    change prodComparison (fgEval P F) M N ≫
      (Types.binaryProductIso ((fgEval P F).obj M) ((fgEval P F).obj N)).hom ≫
        TypeCat.ofHom _root_.Prod.fst = _
    rw [Types.binaryProductIso_hom_comp_fst, prodComparison_fst, ← F.map_comp, hc₁]
    rfl
  have hsnd :
      TypeCat.ofHom (fgProdMap P F M N) ≫ TypeCat.ofHom _root_.Prod.snd =
        F.map c ≫ F.map (ObjectProperty.homMk prod.snd) := by
    change prodComparison (fgEval P F) M N ≫
      (Types.binaryProductIso ((fgEval P F).obj M) ((fgEval P F).obj N)).hom ≫
        TypeCat.ofHom _root_.Prod.snd = _
    rw [Types.binaryProductIso_hom_comp_snd, prodComparison_snd, ← F.map_comp, hc₂]
    rfl
  have hcomp : fgProdMap P F M N = fgAmbientProdMap P F M N ∘ F.map c := by
    funext x
    apply Prod.ext
    · change (TypeCat.ofHom (fgProdMap P F M N) ≫ TypeCat.ofHom _root_.Prod.fst) x =
        (F.map c ≫ F.map (ObjectProperty.homMk prod.fst)) x
      exact ConcreteCategory.congr_hom hfst x
    · change (TypeCat.ofHom (fgProdMap P F M N) ≫ TypeCat.ofHom _root_.Prod.snd) x =
        (F.map c ≫ F.map (ObjectProperty.homMk prod.snd)) x
      exact ConcreteCategory.congr_hom hsnd x
  rw [hcomp]
  exact (Function.Bijective.of_comp_iff _ ((isIso_iff_bijective (F.map c)).mp
    (by infer_instance))).symm

/-- The product comparison of `fgEval` is an isomorphism if and only if `fgProdMap`
is bijective. -/
theorem isIso_prodComparison_iff_bijective_fgProdMap
    (P : ObjectProperty (Over (CommAlgCat.of S R))) [P.ContainsFGTrivSqZeroExt]
    (F : P.FullSubcategory ⥤ Type u) (M N : FGModuleCat.{u} R) :
    IsIso (prodComparison (fgEval P F) M N) ↔ Function.Bijective (fgProdMap P F M N) :=
  (isIso_comp_right_iff (prodComparison (fgEval P F) M N)
    (Types.binaryProductIso ((fgEval P F).obj M) ((fgEval P F).obj N)).hom).symm.trans
      (isIso_iff_bijective _)

/-- If `fgEval` preserves finite products, then `F` is bijective on fibre products
of `R[M]`. -/
theorem BijectiveOnFGSquareZeroProds.of_preservesFiniteProducts
    (P : ObjectProperty (Over (CommAlgCat.of S R))) [P.ContainsFGTrivSqZeroExt]
    (F : P.FullSubcategory ⥤ Type u)
    [PreservesFiniteProducts (fgEval P F)] : F.BijectiveOnFGSquareZeroProds where
  bijective_prod M N := (isIso_prodComparison_iff_bijective_fgProdMap P F M N).mp
    (by infer_instance)

/-- `F(R)` is a singleton if and only if `F(R[0])` is a singleton. -/
theorem unique_overSelf_iff_unique_fgEval_zero
    (P : ObjectProperty (Over (CommAlgCat.of S R))) [P.IsClosedUnderIsomorphisms]
    [P.ContainsFGTrivSqZeroExt] (F : P.FullSubcategory ⥤ Type u) :
    Nonempty (Unique (F.obj (overSelfObj P))) ↔
      Nonempty (Unique ((fgEval P F).obj 0)) := by
  let e : F.obj (overSelfObj P) ≅ (fgEval P F).obj 0 :=
    F.mapIso (P.isoMk (overSelf_iso_fgOverFunctor_zero S R))
  constructor
  · rintro ⟨h⟩
    letI := h
    exact ⟨e.symm.toEquiv.unique⟩
  · rintro ⟨h⟩
    letI := h
    exact ⟨e.toEquiv.unique⟩

/-- If `F(R)` is a singleton, then `F(R[0])` is a singleton. -/
instance instUnique_fgEval_zero [P.IsClosedUnderIsomorphisms] [P.ContainsFGTrivSqZeroExt]
    {F : P.FullSubcategory ⥤ Type u} [Unique (F.obj (overSelfObj P))] :
    Unique ((fgEval P F).obj 0) where
  default := F.map (overSelfObjToFgLiftZero P) default
  uniq x := by
    let e : F.obj (overSelfObj P) ≅ (fgEval P F).obj 0 :=
      F.mapIso (P.isoMk (overSelf_iso_fgOverFunctor_zero S R))
    apply e.symm.toEquiv.injective
    exact Subsingleton.elim _ _

/-- Singleton evaluation at `R` and bijective product comparisons imply that
`M ↦ F(R[M])` preserves finite products. -/
instance instPreservesFiniteProducts_fgEval [P.IsClosedUnderIsomorphisms]
    [P.ContainsFGTrivSqZeroExt] {F : P.FullSubcategory ⥤ Type u}
    [Unique (F.obj (overSelfObj P))] [F.BijectiveOnFGSquareZeroProds] :
    PreservesFiniteProducts (fgEval P F) := by
  letI (M N : FGModuleCat.{u} R) : IsIso (prodComparison (fgEval P F) M N) :=
    (isIso_prodComparison_iff_bijective_fgProdMap P F M N).mpr
      (BijectiveOnFGSquareZeroProds.bijective_prod M N)
  letI : PreservesLimitsOfShape (Discrete WalkingPair) (fgEval P F) :=
    preservesBinaryProducts_of_isIso_prodComparison (fgEval P F)
  letI : PreservesLimit (Functor.empty.{0} (FGModuleCat.{u} R)) (fgEval P F) :=
    preservesLimit_of_preserves_limit_cone
      (HasZeroObject.zeroIsTerminal (C := FGModuleCat.{u} R))
      ((isLimitMapConeEmptyConeEquiv (fgEval P F) 0).symm
        ((Types.isTerminalEquivUnique _).symm inferInstance))
  letI : PreservesLimitsOfShape (Discrete PEmpty.{1}) (fgEval P F) :=
    preservesLimitsOfShape_pempty_of_preservesTerminal (fgEval P F)
  exact PreservesFiniteProducts.of_preserves_binary_and_terminal (fgEval P F)

/-- The unique `R`-linear lift of `M ↦ F(R[M])` through `ModuleCat R ⥤ Type`. -/
theorem module_fgEval (P : ObjectProperty (Over (CommAlgCat.of S R)))
    [P.IsClosedUnderIsomorphisms]
    [P.ContainsFGTrivSqZeroExt] (F : P.FullSubcategory ⥤ Type u)
    [Unique (F.obj (overSelfObj P))] [F.BijectiveOnFGSquareZeroProds] :
    ∃! G : FGModuleCat.{u} R ⥤ ModuleCat.{u} R,
      G.ModuleLinear R ∧ G ⋙ forget (ModuleCat.{u} R) = fgEval P F :=
  FGModuleCat.existsUnique_linearLift (fgEval P F)

end CategoryTheory.Functor
