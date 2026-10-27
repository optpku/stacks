/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import ReasLib.Algebra.Category.CommRingCat.PolynomialResolution.Construction
public import ReasLib.Algebra.Category.CommRingCat.Under.FreeAlgebra
public import ReasLib.AlgebraicGeometry.Scheme.OverSpec
public import ReasLib.AlgebraicTopology.SimplicialObject.Evaluation
public import ReasLib.CategoryTheory.Endofunctor.ComonadResolution.Generators
public import ReasLib.CategoryTheory.Endofunctor.Iteration.Natural
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentSite.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentSite.AffineRealization

/-!
# Standard affine cosimplicial objects in `C_{X/Λ}`

The standard polynomial resolution of the section algebra of an étale chart gives a
functorial cosimplicial affine presentation over that chart.
-/

@[expose] public section

open CategoryTheory
open Opposite
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.Scheme
open MvPolynomial
open scoped AlgebraicGeometry Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Cotangent

variable (Λ : CommRingCat.{u})

/-- The over-object `𝔸(σ; Spec Λ)` in `Over (Spec Λ)`. -/
abbrev affineSpaceOver (σ : Type u) : Over (Spec Λ) :=
  Over.mk (𝔸(σ; Spec Λ) ↘ Spec Λ)

/-- The ring `𝒪_X(U)` as the target of the structure map of `U` over `Spec Λ`. -/
def sectionsUnder {X : AlgebraicSpace (Spec Λ)} (U : smallEtaleSite X) : Under Λ :=
  Under.mk (OverSpec.baseRingHom ((smallEtaleToOver X).obj U))

/-- The generating type of the degree-`n` standard polynomial algebra of `𝒪_X(U)` over `Λ`. -/
def standardGens {X : AlgebraicSpace (Spec Λ)} (U : smallEtaleSite X) (n : SimplexCategory) :
    Type u :=
  (CommRingCat.Under.FreeAlgebra.carrier Λ).obj
    ((Endofunctor.iterate (CommRingCat.Under.FreeAlgebra.comonadFunctor Λ) n.len).obj (sectionsUnder Λ U))

/-- The degree-`n` standard polynomial algebra of `𝒪_X(U)` over `Λ`, as the free `Λ`-algebra
on `standardGens Λ U n`. -/
def standardTerm {X : AlgebraicSpace (Spec Λ)} (U : smallEtaleSite X) (n : SimplexCategory) :
    Under Λ :=
  CommRingCat.Under.FreeAlgebra.algebraic Λ (standardGens Λ U n)

/-- The iterate presentation of `standardTerm` agrees with the free-algebra presentation. -/
theorem standardTerm_eq_iterate {X : AlgebraicSpace (Spec Λ)} (U : smallEtaleSite X)
    (n : SimplexCategory) :
    standardTerm Λ U n =
      (Endofunctor.iterate (CommRingCat.Under.FreeAlgebra.comonadFunctor Λ) (n.len + 1)).obj (sectionsUnder Λ U) :=
  sorry

/-- The augmentation from the `(n+1)`-fold free-algebra iterate onto `𝒪_X(U)`. -/
def standardAugmentationIterate {X : AlgebraicSpace (Spec Λ)} (U : smallEtaleSite X)
    (n : SimplexCategory) :
    (Endofunctor.iterate (CommRingCat.Under.FreeAlgebra.comonadFunctor Λ) (n.len + 1)).obj (sectionsUnder Λ U) ⟶
      sectionsUnder Λ U :=
  Endofunctor.iterate.fold (CommRingCat.Under.FreeAlgebra.comonadFunctor Λ)
    ((CategoryTheory.CommRingCat.Under.PolynomialResolution.counit Λ).app (sectionsUnder Λ U)) (n.len + 1)

/-- The family of global sections classifying `U ⟶ 𝔸(standardGens Λ U n; Spec Λ)`. -/
def standardFamily {X : AlgebraicSpace (Spec Λ)} (U : smallEtaleSite X) (n : SimplexCategory) :
    standardGens Λ U n → Γ(((smallEtaleToOver X).obj U).left, ⊤) :=
  fun x ↦
    (standardAugmentationIterate Λ U n).right (CommRingCat.Under.FreeAlgebra.generator Λ x)

/-- The morphism `U ⟶ 𝔸(standardGens Λ U n; Spec Λ)` over `Spec Λ` classified by
`standardFamily`. -/
def standardOverHom {X : AlgebraicSpace (Spec Λ)} (U : smallEtaleSite X) (n : SimplexCategory) :
    (smallEtaleToOver X).obj U ⟶ affineSpaceOver Λ (standardGens Λ U n) :=
  Over.homMk
    (AffineSpace.homOfVector ((smallEtaleToOver X).obj U).hom (standardFamily Λ U n))
    (AffineSpace.homOfVector_over _ _)

/-- Unfolding of the underlying scheme morphism of `standardOverHom`. -/
theorem standardOverHom_left {X : AlgebraicSpace (Spec Λ)} (U : smallEtaleSite X)
    (n : SimplexCategory) :
    (standardOverHom Λ U n).left =
      AffineSpace.homOfVector ((smallEtaleToOver X).obj U).hom (standardFamily Λ U n) :=
  sorry

/-- The algebra map of iterated standard terms induced by a simplex operator. -/
def standardTermHomIterate {X : AlgebraicSpace (Spec Λ)} (U : smallEtaleSite X)
    {n m : SimplexCategory} (f : n ⟶ m) :
    (Endofunctor.iterate (CommRingCat.Under.FreeAlgebra.comonadFunctor Λ) (m.len + 1)).obj (sectionsUnder Λ U) ⟶
      (Endofunctor.iterate (CommRingCat.Under.FreeAlgebra.comonadFunctor Λ) (n.len + 1)).obj (sectionsUnder Λ U) :=
  (EndofunctorResolution.simplicial.map
      (CategoryTheory.CommRingCat.Under.PolynomialResolution.counit Λ)
      (CategoryTheory.CommRingCat.Under.PolynomialResolution.comultiplication Λ) f.op).app
    (sectionsUnder Λ U)

/-- The polynomial-model image of a generator of the source term under a simplex operator. -/
def standardPolyImage {X : AlgebraicSpace (Spec Λ)} (U : smallEtaleSite X)
    {n m : SimplexCategory} (f : n ⟶ m) (x : standardGens Λ U m) :
    MvPolynomial (standardGens Λ U n) Λ :=
  (CommRingCat.Under.FreeAlgebra.toPolynomial Λ (standardGens Λ U n)).right
    ((standardTermHomIterate Λ U f).right (CommRingCat.Under.FreeAlgebra.generator Λ x))

/-- The family of coordinates of `𝔸(σ_n)` classifying the affine-space map of a simplex
operator. -/
def standardCoordFamily {X : AlgebraicSpace (Spec Λ)} (U : smallEtaleSite X)
    {n m : SimplexCategory} (f : n ⟶ m) :
    standardGens Λ U m → Γ(𝔸(standardGens Λ U n; Spec Λ), ⊤) :=
  fun x ↦
    (MvPolynomial.eval₂Hom
        (((Scheme.ΓSpecIso Λ).inv ≫
            (𝔸(standardGens Λ U n; Spec Λ) ↘ Spec Λ).appTop).hom)
        (AffineSpace.coord (Spec Λ)))
      (standardPolyImage Λ U f x)

/-- The morphism of polynomial affine spaces over `Spec Λ` induced by a simplex operator. -/
def standardAffineSpaceHom {X : AlgebraicSpace (Spec Λ)} (U : smallEtaleSite X)
    {n m : SimplexCategory} (f : n ⟶ m) :
    affineSpaceOver Λ (standardGens Λ U n) ⟶ affineSpaceOver Λ (standardGens Λ U m) :=
  Over.homMk
    (AffineSpace.homOfVector (𝔸(standardGens Λ U n; Spec Λ) ↘ Spec Λ)
      (standardCoordFamily Λ U f))
    (AffineSpace.homOfVector_over _ _)

/-- The `C_{X/Λ}`-component of a simplex operator is the identity on the étale domain. -/
theorem standardAffineMap_w {X : AlgebraicSpace (Spec Λ)} (U : smallEtaleSite X)
    {n m : SimplexCategory} (f : n ⟶ m) :
    (smallEtaleToOver X).map (𝟙 U) ≫ standardOverHom Λ U m =
      standardOverHom Λ U n ≫ standardAffineSpaceHom Λ U f :=
  sorry

/-- The morphism `A_{n,U} ⟶ A_{m,U}` in `C_{X/Λ}` induced by a simplex operator. -/
def standardAffineMap {X : AlgebraicSpace (Spec Λ)} (U : smallEtaleSite X)
    {n m : SimplexCategory} (f : n ⟶ m) :
    ofAffineSpace U (standardGens Λ U n) (standardOverHom Λ U n) ⟶
      ofAffineSpace U (standardGens Λ U m) (standardOverHom Λ U m) where
  left := 𝟙 U
  right := ObjectProperty.homMk (standardAffineSpaceHom Λ U f)
  w := standardAffineMap_w Λ U f

/-- The geometric map of an identity simplex operator is the identity presentation map. -/
theorem standardAffineMap_id {X : AlgebraicSpace (Spec Λ)} (U : smallEtaleSite X)
    (n : SimplexCategory) :
    standardAffineMap Λ U (𝟙 n) = 𝟙 _ :=
  sorry

/-- Geometric simplex maps preserve composition. -/
theorem standardAffineMap_comp {X : AlgebraicSpace (Spec Λ)} (U : smallEtaleSite X)
    {n m k : SimplexCategory} (f : n ⟶ m) (g : m ⟶ k) :
    standardAffineMap Λ U (f ≫ g) =
      standardAffineMap Λ U f ≫ standardAffineMap Λ U g :=
  sorry

/-- The standard affine cosimplicial object over an étale chart. -/
def standardAffineObj {X : AlgebraicSpace (Spec Λ)} (U : smallEtaleSite X) :
    CosimplicialObject (category Λ X) where
  obj n := ofAffineSpace U (standardGens Λ U n) (standardOverHom Λ U n)
  map f := standardAffineMap Λ U f
  map_id := standardAffineMap_id Λ U
  map_comp := standardAffineMap_comp Λ U

/-- The structure map of `U` over `Spec Λ` is compatible with restriction of global sections. -/
theorem sectionsUnderMap_w {X : AlgebraicSpace (Spec Λ)} {U U' : smallEtaleSite X} (g : U' ⟶ U) :
    (sectionsUnder Λ U).hom ≫
        Scheme.Γ.map (((smallEtaleToOver X).map g).left.op) =
      (sectionsUnder Λ U').hom :=
  sorry

/-- The map of section algebras `𝒪_X(U) ⟶ 𝒪_X(U')` induced by `g : U' ⟶ U`. -/
def sectionsUnderMap {X : AlgebraicSpace (Spec Λ)} {U U' : smallEtaleSite X} (g : U' ⟶ U) :
    sectionsUnder Λ U ⟶ sectionsUnder Λ U' :=
  Under.homMk (Scheme.Γ.map (((smallEtaleToOver X).map g).left.op)) (sectionsUnderMap_w Λ g)

/-- The map of iterated standard terms induced by restriction along `g : U' ⟶ U`. -/
def standardTermRestrictIterate {X : AlgebraicSpace (Spec Λ)} {U U' : smallEtaleSite X}
    (g : U' ⟶ U) (n : SimplexCategory) :
    (Endofunctor.iterate (CommRingCat.Under.FreeAlgebra.comonadFunctor Λ) (n.len + 1)).obj (sectionsUnder Λ U) ⟶
      (Endofunctor.iterate (CommRingCat.Under.FreeAlgebra.comonadFunctor Λ) (n.len + 1)).obj (sectionsUnder Λ U') :=
  (Endofunctor.iterate (CommRingCat.Under.FreeAlgebra.comonadFunctor Λ) (n.len + 1)).map (sectionsUnderMap Λ g)

/-- The polynomial-model image of a generator under restriction along `g : U' ⟶ U`. -/
def standardPolyRestrictImage {X : AlgebraicSpace (Spec Λ)} {U U' : smallEtaleSite X}
    (g : U' ⟶ U) (n : SimplexCategory) (x : standardGens Λ U n) :
    MvPolynomial (standardGens Λ U' n) Λ :=
  (CommRingCat.Under.FreeAlgebra.toPolynomial Λ (standardGens Λ U' n)).right
    ((standardTermRestrictIterate Λ g n).right (CommRingCat.Under.FreeAlgebra.generator Λ x))

/-- The family of coordinates classifying restriction of standard affine spaces. -/
def standardRestrictCoordFamily {X : AlgebraicSpace (Spec Λ)} {U U' : smallEtaleSite X}
    (g : U' ⟶ U) (n : SimplexCategory) :
    standardGens Λ U n → Γ(𝔸(standardGens Λ U' n; Spec Λ), ⊤) :=
  fun x ↦
    (MvPolynomial.eval₂Hom
        (((Scheme.ΓSpecIso Λ).inv ≫
            (𝔸(standardGens Λ U' n; Spec Λ) ↘ Spec Λ).appTop).hom)
        (AffineSpace.coord (Spec Λ)))
      (standardPolyRestrictImage Λ g n x)

/-- The morphism `𝔸(σ_{U'}) ⟶ 𝔸(σ_U)` over `Spec Λ` induced by `g : U' ⟶ U`. -/
def standardAffineSpaceRestrict {X : AlgebraicSpace (Spec Λ)} {U U' : smallEtaleSite X}
    (g : U' ⟶ U) (n : SimplexCategory) :
    affineSpaceOver Λ (standardGens Λ U' n) ⟶ affineSpaceOver Λ (standardGens Λ U n) :=
  Over.homMk
    (AffineSpace.homOfVector (𝔸(standardGens Λ U' n; Spec Λ) ↘ Spec Λ)
      (standardRestrictCoordFamily Λ g n))
    (AffineSpace.homOfVector_over _ _)

/-- The `C_{X/Λ}`-commutativity of restriction of standard affine spaces along `g`. -/
theorem standardAffineRestrict_w {X : AlgebraicSpace (Spec Λ)} {U U' : smallEtaleSite X}
    (g : U' ⟶ U) (n : SimplexCategory) :
    (smallEtaleToOver X).map g ≫ standardOverHom Λ U n =
      standardOverHom Λ U' n ≫ standardAffineSpaceRestrict Λ g n :=
  sorry

/-- The morphism `A_{n,U'} ⟶ A_{n,U}` in `C_{X/Λ}` induced by `g : U' ⟶ U`. -/
def standardAffineRestrict {X : AlgebraicSpace (Spec Λ)} {U U' : smallEtaleSite X} (g : U' ⟶ U)
    (n : SimplexCategory) :
    ofAffineSpace U' (standardGens Λ U' n) (standardOverHom Λ U' n) ⟶
      ofAffineSpace U (standardGens Λ U n) (standardOverHom Λ U n) where
  left := g
  right := ObjectProperty.homMk (standardAffineSpaceRestrict Λ g n)
  w := standardAffineRestrict_w Λ g n

/-- Simplex maps commute with restriction along an étale chart morphism. -/
theorem standardAffineObjMap_naturality {X : AlgebraicSpace (Spec Λ)}
    {U U' : smallEtaleSite X} (g : U' ⟶ U)
    {n m : SimplexCategory} (f : n ⟶ m) :
    (standardAffineObj Λ U').map f ≫ standardAffineRestrict Λ g m =
      standardAffineRestrict Λ g n ≫ (standardAffineObj Λ U).map f :=
  sorry

/-- The cosimplicial morphism induced by an étale chart morphism. -/
def standardAffineObjMap {X : AlgebraicSpace (Spec Λ)} {U U' : smallEtaleSite X} (g : U' ⟶ U) :
    standardAffineObj Λ U' ⟶ standardAffineObj Λ U where
  app n := standardAffineRestrict Λ g n
  naturality := fun _ _ f ↦ standardAffineObjMap_naturality Λ g f

/-- Restriction along an identity chart morphism is the identity cosimplicial morphism. -/
theorem standardAffineObjMap_id {X : AlgebraicSpace (Spec Λ)} (U : smallEtaleSite X) :
    standardAffineObjMap Λ (𝟙 U) = 𝟙 _ :=
  sorry

/-- Cosimplicial restriction maps preserve composition of chart morphisms. -/
theorem standardAffineObjMap_comp {X : AlgebraicSpace (Spec Λ)}
    {U V W : smallEtaleSite X} (f : U ⟶ V) (g : V ⟶ W) :
    standardAffineObjMap Λ (f ≫ g) =
      standardAffineObjMap Λ f ≫ standardAffineObjMap Λ g :=
  sorry

/-- The functor `U ↦ A_{•,U}` sending an étale object to its standard affine cosimplicial
object in `C_{X/Λ}`. -/
def standardAffine (X : AlgebraicSpace (Spec Λ)) :
    smallEtaleSite X ⥤ CosimplicialObject (category Λ X) where
  obj U := standardAffineObj Λ U
  map g := standardAffineObjMap Λ g
  map_id := standardAffineObjMap_id Λ
  map_comp := standardAffineObjMap_comp Λ

/-- The affine target in each standard-resolution degree is the spectrum of its section
algebra resolution term. -/
def standardAffineSpecIso (X : AlgebraicSpace (Spec Λ)) (U : smallEtaleSite X)
    (n : SimplexCategory) :
    (affineScheme Λ X).obj (((standardAffine Λ X).obj U).obj n) ≅
      Spec (standardTerm Λ U n).right :=
  let ringIso := (Under.forget Λ).mapIso
    (CommRingCat.Under.FreeAlgebra.polynomialIso Λ (standardGens Λ U n))
  AffineSpace.SpecIso (standardGens Λ U n) Λ ≪≫ Scheme.Spec.mapIso ringIso.op

/-- Unfolding of `standardAffine` on objects. -/
theorem standardAffine_obj (X : AlgebraicSpace (Spec Λ)) (U : smallEtaleSite X)
    (n : SimplexCategory) :
    ((standardAffine Λ X).obj U).obj n =
      ofAffineSpace U (standardGens Λ U n) (standardOverHom Λ U n) :=
  sorry

/-- Each term of `A_{•,U}` lies over `U` in the fibre of `forget Λ X`. -/
theorem standardAffine_forget (X : AlgebraicSpace (Spec Λ)) (U : smallEtaleSite X)
    (n : SimplexCategory) :
    (forget Λ X).obj (((standardAffine Λ X).obj U).obj n) = U :=
  sorry

/-- The functor `A_{•,U} ⋙ forget Λ X` is constantly `U`. -/
theorem standardAffine_comp_forget (X : AlgebraicSpace (Spec Λ)) (U : smallEtaleSite X) :
    (standardAffine Λ X).obj U ⋙ forget Λ X = (Functor.const _).obj U :=
  sorry

/-- All mapping simplicial sets from the standard affine object in the projection fiber
are homotopy equivalent to the point. -/
theorem standardAffine_hasHomSpaces (X : AlgebraicSpace (Spec Λ)) (U : smallEtaleSite X) :
    CosimplicialObject.Pointlike.HasHomSpaces
      (Functor.Fiber.inducedFunctor (standardAffine_comp_forget Λ X U)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Cotangent
