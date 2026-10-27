/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import ReasLib.Algebra.Category.CommRingCat.PolynomialResolution.Construction
public import ReasLib.AlgebraicGeometry.Scheme.OverSpec
public import ReasLib.CategoryTheory.Endofunctor.ComonadResolution.Generators
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Bicategory
public import ReasLib.AlgebraicGeometry.Scheme.CotangentSite.AffineRealization
public import ReasLib.AlgebraicGeometry.Scheme.CotangentSite.Fibered

/-!
# Standard polynomial affine spaces in the fibre of `C_{X/Λ}`

For each open `U` of a `Λ`-scheme `X`, the standard polynomial resolution of
`O_X(U)` over `Λ` produces objects `A_{n,U} = Spec(P_{n,U})` of `C_{X/Λ}` lying
in the fibre over `U`, assembled into a functorial cosimplicial object.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.CommRingCat.Under.PolynomialResolution
open scoped AlgebraicGeometry Simplicial CategoryTheory.IteratedEndofunctor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CotangentSite

/-- The ring of global sections `O_X(U)`. -/
abbrev sectionsRing (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (U : X.smallZariskiSite) : CommRingCat.{u} :=
  Γ(U.left, ⊤)

/-- The structure morphism `Λ ⟶ O_X(U)` induced by `U ⟶ Spec Λ`. -/
def sectionsHom (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (U : X.smallZariskiSite) : Λ ⟶ sectionsRing Λ X U :=
  homToSpecGlobalSectionsEquiv U.left Λ (U.hom ≫ (X ↘ Spec Λ))

/-- Restriction of sections along an open immersion `V ⟶ U` of the small Zariski site. -/
def sectionsRestrict (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    {V U : X.smallZariskiSite} (f : V ⟶ U) :
    sectionsRing Λ X U ⟶ sectionsRing Λ X V :=
  f.left.appTop

/-- The structure maps `Λ ⟶ O_X(U)` are compatible with restriction of sections. -/
theorem sectionsHom_comp (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    {V U : X.smallZariskiSite} (f : V ⟶ U) :
    sectionsHom Λ X U ≫ sectionsRestrict Λ X f = sectionsHom Λ X V :=
  sorry

/-- The algebra `O_X(U)` as an object of `Under Λ`. -/
def standardAlgebra (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (U : X.smallZariskiSite) : Under Λ :=
  Under.mk (sectionsHom Λ X U)

/-- Restriction of `O_X(U)` along `V ⟶ U`, as a morphism of algebras under `Λ`. -/
def standardAlgebraMap (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    {V U : X.smallZariskiSite} (f : V ⟶ U) :
    standardAlgebra Λ X U ⟶ standardAlgebra Λ X V :=
  Under.homMk (sectionsRestrict Λ X f) (sectionsHom_comp Λ X f)

/-- The `n`-fold iterate of the free-algebra comonad applied to `O_X(U)`. -/
def standardIterate (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (n : ℕ) (U : X.smallZariskiSite) : Under Λ :=
  (CategoryTheory.Endofunctor.iterate (functor Λ) n).obj (standardAlgebra Λ X U)

/-- Generator type of the degree-`n` standard polynomial algebra `P_{n,U}`. -/
def standardVars (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (n : ℕ) (U : X.smallZariskiSite) : Type u :=
  (CommRingCat.Under.FreeAlgebra.carrier Λ).obj (standardIterate Λ X n U)

/-- The degree-`n` term of the standard resolution as an object of `Under Λ`. -/
def standardTerm (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (n : SimplexCategory) (U : X.smallZariskiSite) : Under Λ :=
  ((functor Λ) ⁺⦋n.len⦌).obj (standardAlgebra Λ X U)

/-- The iterated counit `P_{n,U} ⟶ O_X(U)` as a morphism of endofunctors. -/
def iterateCounit (Λ : CommRingCat.{u}) :
    (n : ℕ) → (functor Λ) ⁺⦋n⦌ ⟶ 𝟭 (Under Λ)
  | 0 => (Functor.leftUnitor (functor Λ)).hom ≫ counit Λ
  | k + 1 =>
      Functor.whiskerLeft ((functor Λ) ⁺⦋k⦌) (counit Λ) ≫
        (Functor.rightUnitor ((functor Λ) ⁺⦋k⦌)).hom ≫ iterateCounit Λ k

/-- The augmentation `P_{n,U} ⟶ O_X(U)` of the standard resolution, on the free-algebra
model. -/
def standardTermAugmentation (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (n : SimplexCategory) (U : X.smallZariskiSite) :
    standardTerm Λ X n U ⟶ standardAlgebra Λ X U :=
  (iterateCounit Λ n.len).app (standardAlgebra Λ X U)

/-- The MvPolynomial model of the degree-`n` standard term `P_{n,U}`. -/
def standardPolynomial (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (n : SimplexCategory) (U : X.smallZariskiSite) : Under Λ :=
  CommRingCat.Under.FreeAlgebra.polynomial Λ (standardVars Λ X n.len U)

/-- The augmentation `Λ[vars] ⟶ O_X(U)` of the polynomial model of `P_{n,U}`. -/
def standardPolynomialAugmentation (Λ : CommRingCat.{u}) (X : Scheme.{u})
    [X.Over (Spec Λ)] (n : SimplexCategory) (U : X.smallZariskiSite) :
    standardPolynomial Λ X n U ⟶ standardAlgebra Λ X U :=
  (CommRingCat.Under.FreeAlgebra.polynomialIso Λ
      (standardVars Λ X n.len U)).inv ≫
    standardTermAugmentation Λ X n U

/-- The scheme morphism `U ⟶ Spec(P_{n,U})` classified by the standard augmentation. -/
def standardAffineHomScheme (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (n : SimplexCategory) (U : X.smallZariskiSite) :
    U.left ⟶ specPolynomial Λ (standardVars Λ X n.len U) :=
  (homToSpecGlobalSectionsEquiv U.left (standardPolynomial Λ X n U).right).symm
    (standardPolynomialAugmentation Λ X n U).right

/-- The object `A_{n,U} = Spec(P_{n,U})` of `C_{X/Λ}` over `U`. -/
def standardAffine (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (n : SimplexCategory) (U : X.smallZariskiSite) : category Λ X :=
  ofPolynomial U (standardVars Λ X n.len U) (standardAffineHomScheme Λ X n U) sorry

/-- The open of `standardAffine n U` is `U`. -/
theorem standardAffine_U (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (n : SimplexCategory) (U : X.smallZariskiSite) :
    (standardAffine Λ X n U).left = U := rfl

/-- The structure morphism of `standardAffine n U` is `standardAffineHomScheme`. -/
theorem standardAffine_hom (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (n : SimplexCategory) (U : X.smallZariskiSite) :
    (standardAffine Λ X n U).hom.left = standardAffineHomScheme Λ X n U := rfl

/-- The affine-space vertex of `standardAffine n U` is `Spec` of the polynomial model. -/
theorem standardAffine_A (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (n : SimplexCategory) (U : X.smallZariskiSite) :
    (standardAffine Λ X n U).right.obj.left = specPolynomial Λ (standardVars Λ X n.len U) := rfl

/-- The simplicial operator of the standard resolution, transported to polynomial models. -/
def standardPolynomialMap (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    {n m : SimplexCategory} (f : n ⟶ m) (U : X.smallZariskiSite) :
    standardPolynomial Λ X m U ⟶ standardPolynomial Λ X n U :=
  (CommRingCat.Under.FreeAlgebra.polynomialIso Λ
      (standardVars Λ X m.len U)).inv ≫
    ((CategoryTheory.EndofunctorResolution.simplicial.map (counit Λ)
        (comultiplication Λ) f.op).app (standardAlgebra Λ X U)) ≫
    (CommRingCat.Under.FreeAlgebra.polynomialIso Λ
        (standardVars Λ X n.len U)).hom

/-- The morphism `A_{n,U} ⟶ A_{m,U}` in `C_{X/Λ}` induced by a simplex operator. -/
def standardAffineHom (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    {n m : SimplexCategory} (f : n ⟶ m) (U : X.smallZariskiSite) :
    standardAffine Λ X n U ⟶ standardAffine Λ X m U := by
  refine { left := 𝟙 U
           right := ⟨Over.homMk (Spec.map (standardPolynomialMap Λ X f U).right) ?_⟩
           w := ?_ }
  all_goals sorry

/-- The morphism `A_{n,V} ⟶ A_{n,U}` in `C_{X/Λ}` induced by `V ⟶ U`. -/
def standardAffineRestrict (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    {V U : X.smallZariskiSite} (f : V ⟶ U) (n : SimplexCategory) :
    standardAffine Λ X n V ⟶ standardAffine Λ X n U := by
  refine { left := f
           right := ⟨Over.homMk (Spec.map
             ((CommRingCat.Under.FreeAlgebra.polynomialIso Λ
                 (standardVars Λ X n.len U)).inv ≫
               ((functor Λ) ⁺⦋n.len⦌).map (standardAlgebraMap Λ X f) ≫
               (CommRingCat.Under.FreeAlgebra.polynomialIso Λ
                 (standardVars Λ X n.len V)).hom).right) ?_⟩
           w := ?_ }
  all_goals sorry

/-- The forgetful functor `u : C_{X/Λ} ⥤ X_Zar` as a fibred category over `X_Zar`. -/
def fiberedOver (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    FiberedCategoryOver X.smallZariskiSite :=
  FiberedCategoryOver.ofFunctor (forgetZariski Λ X)

/-- The projection of `fiberedOver` is `forgetZariski`. -/
theorem fiberedOver_p (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    (fiberedOver Λ X).p = forgetZariski Λ X := rfl

/-- The standard cosimplicial object `A_{•,U}` in the fibre of `C_{X/Λ}` over `U`. -/
def standardCosimplicial (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (U : X.smallZariskiSite) :
    CosimplicialObject (Functor.Fiber (forgetZariski Λ X) U) := by
  refine { obj := fun n ↦ Functor.Fiber.mk (a := standardAffine Λ X n U) rfl
           map := fun f ↦ ⟨standardAffineHom Λ X f U, Functor.IsHomLift.map (p := forgetZariski Λ X) (standardAffineHom Λ X f U)⟩
           map_id := ?_
           map_comp := ?_ }
  all_goals sorry

/-- Including `standardCosimplicial U` into `C_{X/Λ}` recovers `standardAffine`. -/
theorem standardCosimplicial_obj (Λ : CommRingCat.{u}) (X : Scheme.{u})
    [X.Over (Spec Λ)] (n : SimplexCategory) (U : X.smallZariskiSite) :
    Functor.Fiber.fiberInclusion.obj ((standardCosimplicial Λ X U).obj n) =
      standardAffine Λ X n U := rfl

/-- The fibrewise standard cosimplicial object, viewed in `C_{X/Λ}`. -/
def standardCosimplicialObj (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (U : X.smallZariskiSite) : CosimplicialObject (category Λ X) :=
  standardCosimplicial Λ X U ⋙ Functor.Fiber.fiberInclusion

/-- Degreewise, `standardCosimplicialObj U` is `standardAffine`. -/
theorem standardCosimplicialObj_obj (Λ : CommRingCat.{u}) (X : Scheme.{u})
    [X.Over (Spec Λ)] (n : SimplexCategory) (U : X.smallZariskiSite) :
    (standardCosimplicialObj Λ X U).obj n = standardAffine Λ X n U := rfl

/-- The construction `U ↦ A_{•,U}` as a covariant functor on the small Zariski site. -/
def standardFunctor (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    X.smallZariskiSite ⥤ CosimplicialObject (category Λ X) := by
  refine { obj := fun U ↦ standardCosimplicialObj Λ X U
           map := fun f ↦ { app := fun n ↦ standardAffineRestrict Λ X f n
                            naturality := ?_ }
           map_id := ?_
           map_comp := ?_ }
  all_goals sorry

/-- Evaluating `standardFunctor` at `U` recovers `standardCosimplicialObj U`. -/
theorem standardFunctor_obj (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (U : X.smallZariskiSite) :
    (standardFunctor Λ X).obj U = standardCosimplicialObj Λ X U := rfl

end AlgebraicGeometry.Scheme.CotangentSite
