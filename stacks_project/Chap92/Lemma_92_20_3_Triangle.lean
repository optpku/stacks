/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Definition_92_20_1_Morphism
public import stacks_project.Chap92.Lemma_92_18_3_InverseImage
public import stacks_project.Chap92.Lemma_92_18_8_Triangle
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent.Transitivity
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Cochain
import Mathlib.Tactic.CrossRefAttribute

/-!
# Transitivity triangle of cotangent complexes of morphisms of ringed spaces

For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of ringed spaces, this module owns the
canonical triangle `Lf^* L[g] ⟶ L[f ≫ g] ⟶ L[f] ⟶ Lf^* L[g]⟦1⟧` in `D(O_X)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open HomologicalComplex
open ComplexShape
open Opposite
open AlgebraicTopology
open TopologicalSpace
open CochainComplex
open HomotopyCategory
open SheafOfModules.RingedSite
open scoped Simplicial
open scoped SheafOfModules.RingedSite.CotangentComplex
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

open RingedSpace.Hom

variable {X Y Z : RingedSpace.{u}}

-- Local instance justification (defeq pin): `moduleCategoryHasDerivedCategory` is the reducible standard owner for ringed-site modules; `DerivedCategory.Q` and `distTriang` need that same instance without registering a second derived-category owner.
attribute [local instance] moduleCategoryHasDerivedCategory

/-- The cotangent complex of a morphism of ringed spaces, as an object of `D(O_X)`. -/
abbrev derived (f : X ⟶ Y) : DerivedCategory X.Modules :=
  DerivedCategory.Q.obj (cotangentComplex f)

/-- Unfolding of `derived` as `DerivedCategory.Q` of `cotangentComplex`. -/
theorem derived_eq (f : X ⟶ Y) :
    derived f =
      (DerivedCategory.Q.obj (cotangentComplex f) : DerivedCategory X.Modules) :=
  sorry

/-- Cochain-level extension of scalars of `L(f⁻¹ g♯)` along `f♯`. -/
abbrev pullbackCochain (f : X ⟶ Y) (g : Y ⟶ Z) :
    CochainComplex X.Modules ℤ :=
  ((extendAlong (NaiveCotangent.Tower.second f)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
    (CotangentComplex.obj _ (Under.mk (NaiveCotangent.Tower.first f g)))

/-- Unfolding of `pullbackCochain` as the sheaf-level tensor cochain of the coefficient tower. -/
theorem pullbackCochain_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackCochain f g =
      CotangentComplex.tensorCochain (NaiveCotangent.Tower.first f g)
        (NaiveCotangent.Tower.second f) :=
  sorry

/-- Underived representative of `Lf^* L[g]` in `D(O_X)`, as the image of the tower tensor. -/
abbrev pullbackCotangent (f : X ⟶ Y) (g : Y ⟶ Z) :
    DerivedCategory X.Modules :=
  DerivedCategory.Q.obj (pullbackCochain f g)

/-- Unfolding of `pullbackCotangent` as `DerivedCategory.Q` of `pullbackCochain`. -/
theorem pullbackCotangent_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackCotangent f g =
      (DerivedCategory.Q.obj (pullbackCochain f g) : DerivedCategory X.Modules) :=
  sorry

/-- The under-object of the composite coefficient map `f⁻¹(g⁻¹ O_Z) ⟶ O_X`. -/
abbrev compositeUnder (f : X ⟶ Y) (g : Y ⟶ Z) :=
  Under.mk (NaiveCotangent.Tower.composite f g)

/-- The under-object of the inverse-image structure map of the composite `f ≫ g`. -/
abbrev compositionUnder (f : X ⟶ Y) (g : Y ⟶ Z) :=
  Under.mk (inverseImageStructureSheafHomComm (f ≫ g))

/-- The inverse-image coefficient sheaf `(f ≫ g)⁻¹ O_Z`. -/
abbrev compositionSource (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).hom.base).obj Z.sheaf

/-- Termwise ring-sheaf map of standard-resolution algebras induced by `Tower.sourceIso`. -/
def compositionTermHom (f : X ⟶ Y) (g : Y ⟶ Z) (n : SimplexCategoryᵒᵖ) :
    (CotangentComplex.standardTerm (NaiveCotangent.Tower.source f g)
        (compositeUnder f g) n).right ⟶
      (CotangentComplex.standardTerm (compositionSource f g)
        (compositionUnder f g) n).right :=
  CotangentComplex.standardTermRightHom (NaiveCotangent.Tower.sourceIso f g).hom
    (𝟙 X.sheaf) n

/-- Inverse termwise ring-sheaf map of standard-resolution algebras along `Tower.sourceIso`. -/
def compositionTermHomInv (f : X ⟶ Y) (g : Y ⟶ Z) (n : SimplexCategoryᵒᵖ) :
    (CotangentComplex.standardTerm (compositionSource f g)
        (compositionUnder f g) n).right ⟶
      (CotangentComplex.standardTerm (NaiveCotangent.Tower.source f g)
        (compositeUnder f g) n).right :=
  CotangentComplex.standardTermRightHom (NaiveCotangent.Tower.sourceIso f g).inv
    (𝟙 X.sheaf) n

/-- Compatibility of `Tower.sourceIso.hom` with the structure maps of `O_X`. -/
theorem compositionSourceSquare_w (f : X ⟶ Y) (g : Y ⟶ Z) :
    (NaiveCotangent.Tower.sourceIso f g).hom ≫ (compositionUnder f g).hom =
      (compositeUnder f g).hom ≫ 𝟙 X.sheaf :=
  sorry

/-- Compatibility of `Tower.sourceIso.inv` with the structure maps of `O_X`. -/
theorem compositionSourceSquareInv_w (f : X ⟶ Y) (g : Y ⟶ Z) :
    (NaiveCotangent.Tower.sourceIso f g).inv ≫ (compositeUnder f g).hom =
      (compositionUnder f g).hom ≫ 𝟙 X.sheaf :=
  sorry

/-- Structure maps of standard-resolution terms form a commutative square along `Tower.sourceIso`. -/
theorem compositionTermSquare (f : X ⟶ Y) (g : Y ⟶ Z) (n : SimplexCategoryᵒᵖ) :
    CommSq (NaiveCotangent.Tower.sourceIso f g).hom
      (CotangentComplex.standardTerm (NaiveCotangent.Tower.source f g)
        (compositeUnder f g) n).hom
      (CotangentComplex.standardTerm (compositionSource f g)
        (compositionUnder f g) n).hom
      (compositionTermHom f g n) :=
  ⟨sorry⟩

/-- Inverse structure maps of standard-resolution terms form a commutative square along
`Tower.sourceIso`. -/
theorem compositionTermSquareInv (f : X ⟶ Y) (g : Y ⟶ Z) (n : SimplexCategoryᵒᵖ) :
    CommSq (NaiveCotangent.Tower.sourceIso f g).inv
      (CotangentComplex.standardTerm (compositionSource f g)
        (compositionUnder f g) n).hom
      (CotangentComplex.standardTerm (NaiveCotangent.Tower.source f g)
        (compositeUnder f g) n).hom
      (compositionTermHomInv f g n) :=
  ⟨sorry⟩

/-- Termwise base-change of relative differentials along `compositionTermSquare`. -/
def compositionDifferentialsMap (f : X ⟶ Y) (g : Y ⟶ Z) (n : SimplexCategoryᵒᵖ) :
    relativeDifferentials.{u, u}
        (CotangentComplex.standardTerm (NaiveCotangent.Tower.source f g)
          (compositeUnder f g) n).hom ⟶
      (restrictionAlong (compositionTermHom f g n)).obj
        (relativeDifferentials.{u, u}
          (CotangentComplex.standardTerm (compositionSource f g)
            (compositionUnder f g) n).hom) :=
  RelativeDifferentials.map (C := Opens X) (J := Opens.grothendieckTopology X)
    (compositionTermSquare f g n)


/-- Termwise inverse base-change of relative differentials along `compositionTermSquareInv`. -/
def compositionDifferentialsMapInv (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : SimplexCategoryᵒᵖ) :
    relativeDifferentials.{u, u}
        (CotangentComplex.standardTerm (compositionSource f g)
          (compositionUnder f g) n).hom ⟶
      (restrictionAlong (compositionTermHomInv f g n)).obj
        (relativeDifferentials.{u, u}
          (CotangentComplex.standardTerm (NaiveCotangent.Tower.source f g)
            (compositeUnder f g) n).hom) :=
  RelativeDifferentials.map (C := Opens X) (J := Opens.grothendieckTopology X)
    (compositionTermSquareInv f g n)

/-- Restriction of relative differentials along `compositionTermHom` agrees with restriction
of the target simplicial cotangent term along the source augmentation. -/
theorem compositionRestrictedTarget_eq (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : SimplexCategoryᵒᵖ) :
    (restrictionAlong (compositionTermHom f g n)).obj
        (relativeDifferentials.{u, u}
          (CotangentComplex.standardTerm (compositionSource f g)
            (compositionUnder f g) n).hom) =
      (restrictionAlong
          (CotangentComplex.standardAugmentation
            (NaiveCotangent.Tower.source f g) (compositeUnder f g) n)).obj
        ((CotangentComplex.simplicialModule (compositionSource f g)
            (compositionUnder f g)).obj n) :=
  sorry

/-- The `Ω`-level source-change map, transported to the restriction of the target simplicial
term along the source augmentation. -/
def compositionRestrictedMap (f : X ⟶ Y) (g : Y ⟶ Z) (n : SimplexCategoryᵒᵖ) :
    relativeDifferentials.{u, u}
        (CotangentComplex.standardTerm (NaiveCotangent.Tower.source f g)
          (compositeUnder f g) n).hom ⟶
      (restrictionAlong
          (CotangentComplex.standardAugmentation
            (NaiveCotangent.Tower.source f g) (compositeUnder f g) n)).obj
        ((CotangentComplex.simplicialModule (compositionSource f g)
            (compositionUnder f g)).obj n) :=
  compositionDifferentialsMap f g n ≫ eqToHom (compositionRestrictedTarget_eq f g n)

/-- Unfolding of `compositionRestrictedMap` through `eqToHom`. -/
theorem compositionRestrictedMap_eq (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : SimplexCategoryᵒᵖ) :
    compositionRestrictedMap f g n =
      compositionDifferentialsMap f g n ≫
        eqToHom (compositionRestrictedTarget_eq f g n) :=
  sorry

/-- Degreewise source-change map of simplicial cotangent modules along `Tower.sourceIso`. -/
def compositionSimplicialMap (f : X ⟶ Y) (g : Y ⟶ Z) (n : SimplexCategoryᵒᵖ) :
    (CotangentComplex.simplicialModule (NaiveCotangent.Tower.source f g)
        (compositeUnder f g)).obj n ⟶
      (CotangentComplex.simplicialModule (compositionSource f g)
        (compositionUnder f g)).obj n :=
  ((extendRestrictAdj
        (CotangentComplex.standardAugmentation (NaiveCotangent.Tower.source f g)
          (compositeUnder f g) n)).homEquiv _ _).symm
    (compositionRestrictedMap f g n)

/-- Unfolding of `compositionSimplicialMap` through the extension-restriction adjunction. -/
theorem compositionSimplicialMap_eq (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : SimplexCategoryᵒᵖ) :
    compositionSimplicialMap f g n =
      ((extendRestrictAdj
          (CotangentComplex.standardAugmentation (NaiveCotangent.Tower.source f g)
            (compositeUnder f g) n)).homEquiv _ _).symm
        (compositionRestrictedMap f g n) :=
  sorry

/-- Restriction of relative differentials along `compositionTermHomInv` agrees with restriction
of the source simplicial cotangent term along the target augmentation. -/
theorem compositionRestrictedTargetInv_eq (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : SimplexCategoryᵒᵖ) :
    (restrictionAlong (compositionTermHomInv f g n)).obj
        (relativeDifferentials.{u, u}
          (CotangentComplex.standardTerm (NaiveCotangent.Tower.source f g)
            (compositeUnder f g) n).hom) =
      (restrictionAlong
          (CotangentComplex.standardAugmentation (compositionSource f g)
            (compositionUnder f g) n)).obj
        ((CotangentComplex.simplicialModule (NaiveCotangent.Tower.source f g)
            (compositeUnder f g)).obj n) :=
  sorry

/-- The inverse `Ω`-level source-change map, transported to the restriction of the source
simplicial term along the target augmentation. -/
def compositionRestrictedMapInv (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : SimplexCategoryᵒᵖ) :
    relativeDifferentials.{u, u}
        (CotangentComplex.standardTerm (compositionSource f g)
          (compositionUnder f g) n).hom ⟶
      (restrictionAlong
          (CotangentComplex.standardAugmentation (compositionSource f g)
            (compositionUnder f g) n)).obj
        ((CotangentComplex.simplicialModule (NaiveCotangent.Tower.source f g)
            (compositeUnder f g)).obj n) :=
  compositionDifferentialsMapInv f g n ≫
    eqToHom (compositionRestrictedTargetInv_eq f g n)

/-- Unfolding of `compositionRestrictedMapInv` through `eqToHom`. -/
theorem compositionRestrictedMapInv_eq (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : SimplexCategoryᵒᵖ) :
    compositionRestrictedMapInv f g n =
      compositionDifferentialsMapInv f g n ≫
        eqToHom (compositionRestrictedTargetInv_eq f g n) :=
  sorry

/-- Degreewise inverse source-change map of simplicial cotangent modules along `Tower.sourceIso`. -/
def compositionSimplicialMapInv (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : SimplexCategoryᵒᵖ) :
    (CotangentComplex.simplicialModule (compositionSource f g)
        (compositionUnder f g)).obj n ⟶
      (CotangentComplex.simplicialModule (NaiveCotangent.Tower.source f g)
        (compositeUnder f g)).obj n :=
  ((extendRestrictAdj
        (CotangentComplex.standardAugmentation (compositionSource f g)
          (compositionUnder f g) n)).homEquiv _ _).symm
    (compositionRestrictedMapInv f g n)

/-- Unfolding of `compositionSimplicialMapInv` through the extension-restriction adjunction. -/
theorem compositionSimplicialMapInv_eq (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : SimplexCategoryᵒᵖ) :
    compositionSimplicialMapInv f g n =
      ((extendRestrictAdj
          (CotangentComplex.standardAugmentation (compositionSource f g)
            (compositionUnder f g) n)).homEquiv _ _).symm
        (compositionRestrictedMapInv f g n) :=
  sorry

/-- Degreewise source-change isomorphism of simplicial cotangent modules along `Tower.sourceIso`. -/
def compositionTermIso (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    (CotangentComplex.simplicialModule (NaiveCotangent.Tower.source f g)
        (compositeUnder f g)).obj (Opposite.op ({ len := n } : SimplexCategory)) ≅
      (CotangentComplex.simplicialModule (compositionSource f g)
        (compositionUnder f g)).obj (Opposite.op ({ len := n } : SimplexCategory)) where
  hom := compositionSimplicialMap f g (Opposite.op ({ len := n } : SimplexCategory))
  inv := compositionSimplicialMapInv f g (Opposite.op ({ len := n } : SimplexCategory))
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Identification of the extended cochain term of `L(Tower.composite f g)` with the
unextended simplicial term in degree `n`. -/
def compositionXIso (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    (CotangentComplex.obj _ (compositeUnder f g)).X (-n) ≅
      (CotangentComplex.simplicialModule (NaiveCotangent.Tower.source f g)
        (compositeUnder f g)).obj (Opposite.op ({ len := n } : SimplexCategory)) :=
  extendXIso
      ((alternatingFaceMapComplex X.Modules).obj
        (CotangentComplex.simplicialModule (NaiveCotangent.Tower.source f g)
          (compositeUnder f g)))
      embeddingDownNat (rfl : embeddingDownNat.f n = -n)

/-- Identification of the extended cochain term of `L[f ≫ g]` with the unextended simplicial
term in degree `n`. -/
def compositionTargetXIso (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    (cotangentComplex (f ≫ g)).X (-n) ≅
      (CotangentComplex.simplicialModule (compositionSource f g)
        (compositionUnder f g)).obj (Opposite.op ({ len := n } : SimplexCategory)) :=
  extendXIso
      ((alternatingFaceMapComplex X.Modules).obj
        (CotangentComplex.simplicialModule (compositionSource f g)
          (compositionUnder f g)))
      embeddingDownNat (rfl : embeddingDownNat.f n = -n)

/-- Degreewise comparison of `L(Tower.composite f g)` with `L[f ≫ g]`. -/
def compositionAppIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∀ n : ℤ,
      (CotangentComplex.obj _ (compositeUnder f g)).X n ≅
        (cotangentComplex (f ≫ g)).X n
  | Int.ofNat (Nat.succ k) =>
      { hom :=
          (0 :
            (CotangentComplex.obj _ (compositeUnder f g)).X (Int.ofNat k.succ) ⟶
              (cotangentComplex (f ≫ g)).X (Int.ofNat k.succ))
        inv :=
          (0 :
            (cotangentComplex (f ≫ g)).X (Int.ofNat k.succ) ⟶
              (CotangentComplex.obj _ (compositeUnder f g)).X (Int.ofNat k.succ))
        hom_inv_id := sorry
        inv_hom_id := sorry }
  | (0 : ℤ) =>
      (compositionXIso f g 0).trans
        ((compositionTermIso f g 0).trans (compositionTargetXIso f g 0).symm)
  | Int.negSucc k =>
      (compositionXIso f g k.succ).trans
        ((compositionTermIso f g k.succ).trans
          (compositionTargetXIso f g k.succ).symm)

/-- Changing from the iterated inverse-image coefficient sheaf to the inverse image along the
composite identifies `L(Tower.composite f g)` with `L[f ≫ g]`. -/
def compositionIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    CotangentComplex.obj _ (compositeUnder f g) ≅ cotangentComplex (f ≫ g) :=
  HomologicalComplex.Hom.isoOfComponents (compositionAppIso f g) (fun _ _ _ ↦ sorry)

/-- In degree `n`, the forward map of `compositionIso` is `compositionAppIso`. -/
theorem compositionIso_hom (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℤ) :
    (compositionIso f g).hom.f n = (compositionAppIso f g n).hom :=
  sorry

/-- In degree `n`, the inverse map of `compositionIso` is the inverse of `compositionAppIso`. -/
theorem compositionIso_inv (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℤ) :
    (compositionIso f g).inv.f n = (compositionAppIso f g n).inv :=
  sorry

/-- The unextended first transitivity map `Lf^* L[g] ⟶ L[f ≫ g]`. -/
def transitivityMapCochain (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackCochain f g ⟶ cotangentComplex (f ≫ g) :=
  CotangentComplex.tensorMapCochain (NaiveCotangent.Tower.first f g)
      (NaiveCotangent.Tower.second f) ≫
    (compositionIso f g).hom

/-- The first map `Lf^* L[g] ⟶ L[f ≫ g]` of the transitivity triangle in `D(O_X)`. -/
def transitivityMap (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackCotangent f g ⟶ derived (f ≫ g) :=
  DerivedCategory.Q.map (transitivityMapCochain f g)

/-- Unfolding of `transitivityMap` as `DerivedCategory.Q.map` of `transitivityMapCochain`. -/
theorem transitivityMap_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    transitivityMap f g = DerivedCategory.Q.map (transitivityMapCochain f g) :=
  sorry

/-- The unextended second transitivity map `L[f ≫ g] ⟶ L[f]`. -/
def toRelativeMapCochain (f : X ⟶ Y) (g : Y ⟶ Z) :
    cotangentComplex (f ≫ g) ⟶ cotangentComplex f :=
  (compositionIso f g).inv ≫
    CotangentComplex.toRelativeMapCochain (NaiveCotangent.Tower.first f g)
      (NaiveCotangent.Tower.second f)

/-- The second map `L[f ≫ g] ⟶ L[f]` of the transitivity triangle in `D(O_X)`. -/
def toRelativeMap (f : X ⟶ Y) (g : Y ⟶ Z) :
    derived (f ≫ g) ⟶ derived f :=
  DerivedCategory.Q.map (toRelativeMapCochain f g)

/-- Unfolding of `toRelativeMap` as `DerivedCategory.Q.map` of `toRelativeMapCochain`. -/
theorem toRelativeMap_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    toRelativeMap f g = DerivedCategory.Q.map (toRelativeMapCochain f g) :=
  sorry

/-- The connecting map `L[f] ⟶ (Lf^* L[g])⟦1⟧` of the transitivity triangle. -/
def connectingMap (f : X ⟶ Y) (g : Y ⟶ Z) :
    derived f ⟶ (pullbackCotangent f g)⟦(1 : ℤ)⟧ :=
  CotangentComplex.connectingMap (NaiveCotangent.Tower.first f g)
    (NaiveCotangent.Tower.second f)

/-- Unfolding of `connectingMap` as the sheaf-level connecting map of the coefficient tower. -/
theorem connectingMap_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    connectingMap f g =
      CotangentComplex.connectingMap (NaiveCotangent.Tower.first f g)
        (NaiveCotangent.Tower.second f) :=
  sorry

/-- The displayed transitivity triangle of cotangent complexes of morphisms of ringed spaces
in `D(O_X)`. -/
def transitivityTriangle (f : X ⟶ Y) (g : Y ⟶ Z) :
    Triangle (DerivedCategory X.Modules) :=
  Triangle.mk (transitivityMap f g) (toRelativeMap f g) (connectingMap f g)

/-- The first vertex of `transitivityTriangle` is `pullbackCotangent`. -/
theorem transitivityTriangle_obj₁ (f : X ⟶ Y) (g : Y ⟶ Z) :
    (transitivityTriangle f g).obj₁ = pullbackCotangent f g :=
  sorry

/-- The second vertex of `transitivityTriangle` is `derived (f ≫ g)`. -/
theorem transitivityTriangle_obj₂ (f : X ⟶ Y) (g : Y ⟶ Z) :
    (transitivityTriangle f g).obj₂ = derived (f ≫ g) :=
  sorry

/-- The third vertex of `transitivityTriangle` is `derived f`. -/
theorem transitivityTriangle_obj₃ (f : X ⟶ Y) (g : Y ⟶ Z) :
    (transitivityTriangle f g).obj₃ = derived f :=
  sorry

/-- The first morphism of `transitivityTriangle` is `transitivityMap`. -/
theorem transitivityTriangle_mor₁ (f : X ⟶ Y) (g : Y ⟶ Z) :
    (transitivityTriangle f g).mor₁ = transitivityMap f g :=
  sorry

/-- The second morphism of `transitivityTriangle` is `toRelativeMap`. -/
theorem transitivityTriangle_mor₂ (f : X ⟶ Y) (g : Y ⟶ Z) :
    (transitivityTriangle f g).mor₂ = toRelativeMap f g :=
  sorry

/-- The third morphism of `transitivityTriangle` is `connectingMap`. -/
theorem transitivityTriangle_mor₃ (f : X ⟶ Y) (g : Y ⟶ Z) :
    (transitivityTriangle f g).mor₃ = connectingMap f g :=
  sorry

/-- Canonical identification `f⁻¹ L[g] ≅ L(f⁻¹ g♯)` of complexes of `f⁻¹ O_Y`-modules. -/
def inverseImageCotangentIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    CotangentComplex.InverseImage.source (opensMorphismOfTopoi f)
        (inverseImageStructureSheafHomComm g) ≅
      CotangentComplex.InverseImage.target (opensMorphismOfTopoi f)
        (inverseImageStructureSheafHomComm g) :=
  CotangentComplex.InverseImage.iso (opensMorphismOfTopoi f)
    (inverseImageStructureSheafHomComm g)

/-- Unfolding of `inverseImageCotangentIso` as the topos-level inverse-image comparison. -/
theorem inverseImageCotangentIso_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    inverseImageCotangentIso f g =
      CotangentComplex.InverseImage.iso (opensMorphismOfTopoi f)
        (inverseImageStructureSheafHomComm g) :=
  sorry

/-- Extending scalars along `f♯` identifies `f^* L[g]` with the tower tensor of
`f⁻¹ L[g]`. -/
def pullbackIso_inverseImage (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((RingedSpace.Hom.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (cotangentComplex g) ≅
      ((extendAlong (NaiveCotangent.Tower.second f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((SheafOfModules.RingedSite.InverseImage.modulePullback
              (Opens.map f.hom.base) Y.sheaf).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (cotangentComplex g)) :=
  SheafOfModules.RingedSite.InverseImage.Factorization.complexObjIso
    (J := Opens.grothendieckTopology Y) (K := Opens.grothendieckTopology X)
    (Opens.map f.hom.base) (ComplexShape.up ℤ)
    (RingedSpace.Hom.commRingSheafPushforwardMap f) (cotangentComplex g)

/-- The forward map of `pullbackIso_inverseImage` is the module-pullback factorization. -/
theorem pullbackIso_inverseImage_hom (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pullbackIso_inverseImage f g).hom =
      (SheafOfModules.RingedSite.InverseImage.Factorization.complexObjIso
          (J := Opens.grothendieckTopology Y) (K := Opens.grothendieckTopology X)
          (Opens.map f.hom.base) (ComplexShape.up ℤ)
          (RingedSpace.Hom.commRingSheafPushforwardMap f)
          (cotangentComplex g)).hom :=
  sorry

/-- Cochain-level comparison `L(f)^*.obj (derived g) ⟶ Q((f^* L[g]))`, an isomorphism
by termwise flatness of `f⁻¹ L[g]` from Lemma 92.18.3. -/
def pullbackDerivedCounit (f : X ⟶ Y) (g : Y ⟶ Z)
    [(RingedSpace.Hom.pullback f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)] :
    (modulePullbackDerived f).obj (derived g) ⟶
      DerivedCategory.Q.obj
        (((RingedSpace.Hom.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (cotangentComplex g)) :=
  (modulePullbackDerived f).map
      ((DerivedCategory.quotientCompQhIso Y.Modules).inv.app (cotangentComplex g)) ≫
    ((modulePullbackToDerived f).totalLeftDerivedCounit
        DerivedCategory.Qh (ModuleQis Y)).app
      ((HomotopyCategory.quotient Y.Modules (ComplexShape.up ℤ)).obj
        (cotangentComplex g)) ≫
    (Functor.Homotopy.cochainIso (RingedSpace.Hom.pullback f)).hom.app
      (cotangentComplex g)

/-- The comparison `pullbackDerivedCounit` is an isomorphism by termwise flatness of
`f⁻¹ L[g]`. -/
instance pullbackDerivedCounit_isIso (f : X ⟶ Y) (g : Y ⟶ Z)
    [(RingedSpace.Hom.pullback f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)] :
    IsIso (pullbackDerivedCounit f g) :=
  sorry

/-- Identification of the underived tower tensor `pullbackCotangent f g` with
`(modulePullbackDerived f).obj (derived g)`, using termwise flatness of `f⁻¹ L[g]`
from Lemma 92.18.3 so that `L(f)^*` agrees with underived extension of scalars. -/
def pullbackIso_derived (f : X ⟶ Y) (g : Y ⟶ Z)
    [(RingedSpace.Hom.pullback f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)] :
    DerivedCategory.Q.obj
        (((RingedSpace.Hom.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (cotangentComplex g)) ≅
      (modulePullbackDerived f).obj (derived g) :=
  (asIso (pullbackDerivedCounit f g)).symm

/-- The inverse of `pullbackIso_derived` is `pullbackDerivedCounit`. -/
theorem pullbackIso_derived_inv (f : X ⟶ Y) (g : Y ⟶ Z)
    [(RingedSpace.Hom.pullback f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)] :
    (pullbackIso_derived f g).inv = pullbackDerivedCounit f g :=
  sorry

end AlgebraicGeometry.RingedSpace
