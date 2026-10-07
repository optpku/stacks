module

public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Products
public import stacks_project.Chap90.Lemma_90_11_4
public import stacks_project.Chap90.Lemma_90_11_8_FGOver

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
  property := sorry

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
  bijective_prod _ _ := sorry

/-- Bijectivity of the ambient fibre-product map is equivalent to bijectivity of
`fgProdMap`. -/
theorem fgAmbientProdMap_bijective_iff (P : ObjectProperty (Over (CommAlgCat.of S R)))
    [P.IsClosedUnderIsomorphisms]
    [P.ContainsFGTrivSqZeroExt] (F : P.FullSubcategory ⥤ Type u)
    (M N : FGModuleCat.{u} R) :
    Function.Bijective (fgAmbientProdMap P F M N) ↔
      Function.Bijective (fgProdMap P F M N) := sorry

/-- The product comparison of `fgEval` is an isomorphism if and only if `fgProdMap`
is bijective. -/
theorem isIso_prodComparison_iff_bijective_fgProdMap
    (P : ObjectProperty (Over (CommAlgCat.of S R))) [P.ContainsFGTrivSqZeroExt]
    (F : P.FullSubcategory ⥤ Type u) (M N : FGModuleCat.{u} R) :
    IsIso (prodComparison (fgEval P F) M N) ↔ Function.Bijective (fgProdMap P F M N) :=
  sorry

/-- If `fgEval` preserves finite products, then `F` is bijective on fibre products
of `R[M]`. This is not an instance, to avoid a loop with
`instPreservesFiniteProducts_fgEval`. -/
theorem BijectiveOnFGSquareZeroProds.of_preservesFiniteProducts
    (P : ObjectProperty (Over (CommAlgCat.of S R))) [P.ContainsFGTrivSqZeroExt]
    (F : P.FullSubcategory ⥤ Type u)
    [PreservesFiniteProducts (fgEval P F)] : F.BijectiveOnFGSquareZeroProds := sorry

/-- `F(R)` is a singleton if and only if `F(R[0])` is a singleton. -/
theorem unique_overSelf_iff_unique_fgEval_zero
    (P : ObjectProperty (Over (CommAlgCat.of S R))) [P.IsClosedUnderIsomorphisms]
    [P.ContainsFGTrivSqZeroExt] (F : P.FullSubcategory ⥤ Type u) :
    Nonempty (Unique (F.obj (overSelfObj P))) ↔
      Nonempty (Unique ((fgEval P F).obj 0)) := sorry

/-- If `F(R)` is a singleton, then `F(R[0])` is a singleton. -/
instance instUnique_fgEval_zero [P.IsClosedUnderIsomorphisms] [P.ContainsFGTrivSqZeroExt]
    {F : P.FullSubcategory ⥤ Type u} [Unique (F.obj (overSelfObj P))] :
    Unique ((fgEval P F).obj 0) where
  default := F.map (overSelfObjToFgLiftZero P) default
  uniq := sorry

/-- Under the source hypotheses, `M ↦ F(R[M])` preserves finite products. -/
instance instPreservesFiniteProducts_fgEval [P.IsClosedUnderIsomorphisms]
    [P.ContainsFGTrivSqZeroExt] {F : P.FullSubcategory ⥤ Type u}
    [Unique (F.obj (overSelfObj P))] [F.BijectiveOnFGSquareZeroProds] :
    PreservesFiniteProducts (fgEval P F) := sorry

/-- The unique `R`-linear lift of `M ↦ F(R[M])` through `ModuleCat R ⥤ Type`. -/
theorem existsUnique_linearLift_fgEval (P : ObjectProperty (Over (CommAlgCat.of S R)))
    [P.IsClosedUnderIsomorphisms]
    [P.ContainsFGTrivSqZeroExt] (F : P.FullSubcategory ⥤ Type u)
    [Unique (F.obj (overSelfObj P))] [F.BijectiveOnFGSquareZeroProds] :
    ∃! G : FGModuleCat.{u} R ⥤ ModuleCat.{u} R,
      G.ModuleLinear R ∧ G ⋙ forget (ModuleCat.{u} R) = fgEval P F := sorry

/-- The values `F(R[M])` carry the `R`-module structure of `instModule` on `fgEval`. -/
@[reducible]
def instModule_fgEval (P : ObjectProperty (Over (CommAlgCat.of S R)))
    [P.IsClosedUnderIsomorphisms] [P.ContainsFGTrivSqZeroExt]
    (F : P.FullSubcategory ⥤ Type u) [Unique (F.obj (overSelfObj P))]
    [F.BijectiveOnFGSquareZeroProds] (M : FGModuleCat.{u} R) :
    Module R ((fgEval P F).obj M) :=
  instModule (fgEval P F) M

/-- `instModule_fgEval` is the `instModule` structure on `fgEval`. -/
theorem instModule_fgEval_eq (P : ObjectProperty (Over (CommAlgCat.of S R)))
    [P.IsClosedUnderIsomorphisms] [P.ContainsFGTrivSqZeroExt]
    (F : P.FullSubcategory ⥤ Type u) [Unique (F.obj (overSelfObj P))]
    [F.BijectiveOnFGSquareZeroProds] (M : FGModuleCat.{u} R) :
    instModule_fgEval P F M = instModule (fgEval P F) M := rfl

end CategoryTheory.Functor
