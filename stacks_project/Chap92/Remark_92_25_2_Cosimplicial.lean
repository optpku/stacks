module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import ReasLib.Algebra.Category.CommRingCat.PolynomialResolution.Construction
public import ReasLib.AlgebraicGeometry.Scheme.OverSpec
public import ReasLib.CategoryTheory.Endofunctor.ComonadResolution.Generators
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Bicategory
public import stacks_project.Chap92.Lemma_92_25_1_Fibered

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
  homToSpecGlobalSectionsEquiv U.left Λ (U.left ↘ Spec Λ)

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
    (n : SimplexCategory) (U : X.smallZariskiSite) : Obj Λ X :=
  Obj.of U (standardVars Λ X n.len U) (standardAffineHomScheme Λ X n U) sorry

/-- The open of `standardAffine n U` is `U`. -/
theorem standardAffine_U (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (n : SimplexCategory) (U : X.smallZariskiSite) :
    (standardAffine Λ X n U).U = U :=
  sorry

/-- The variable type of `standardAffine n U` is the generator type of `P_{n,U}`. -/
theorem standardAffine_vars (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (n : SimplexCategory) (U : X.smallZariskiSite) :
    (standardAffine Λ X n U).vars = standardVars Λ X n.len U :=
  sorry

/-- The structure morphism of `standardAffine n U` is `standardAffineHomScheme`. -/
theorem standardAffine_hom (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (n : SimplexCategory) (U : X.smallZariskiSite) :
    (standardAffine Λ X n U).hom = standardAffineHomScheme Λ X n U :=
  sorry

/-- The affine-space vertex of `standardAffine n U` is `Spec` of the polynomial model. -/
theorem standardAffine_A (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (n : SimplexCategory) (U : X.smallZariskiSite) :
    (standardAffine Λ X n U).A = specPolynomial Λ (standardVars Λ X n.len U) :=
  sorry

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
    standardAffine Λ X n U ⟶ standardAffine Λ X m U where
  left := 𝟙 U
  right := Spec.map (standardPolynomialMap Λ X f U).right
  isOver := sorry
  w := sorry

/-- The morphism `A_{n,V} ⟶ A_{n,U}` in `C_{X/Λ}` induced by `V ⟶ U`. -/
def standardAffineRestrict (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    {V U : X.smallZariskiSite} (f : V ⟶ U) (n : SimplexCategory) :
    standardAffine Λ X n V ⟶ standardAffine Λ X n U where
  left := f
  right :=
    Spec.map
      ((CommRingCat.Under.FreeAlgebra.polynomialIso Λ
            (standardVars Λ X n.len U)).inv ≫
          ((functor Λ) ⁺⦋n.len⦌).map (standardAlgebraMap Λ X f) ≫
          (CommRingCat.Under.FreeAlgebra.polynomialIso Λ
              (standardVars Λ X n.len V)).hom).right
  isOver := sorry
  w := sorry

/-- The forgetful functor `u : C_{X/Λ} ⥤ X_Zar` as a fibred category over `X_Zar`. -/
def fiberedOver (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    FiberedCategoryOver X.smallZariskiSite :=
  FiberedCategoryOver.ofFunctor (forgetZariski Λ X)

/-- The projection of `fiberedOver` is `forgetZariski`. -/
theorem fiberedOver_p (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    (fiberedOver Λ X).p = forgetZariski Λ X :=
  sorry

/-- The standard cosimplicial object `A_{•,U}` in the fibre of `C_{X/Λ}` over `U`. -/
def standardCosimplicial (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (U : X.smallZariskiSite) :
    CosimplicialObject (Functor.Fiber (forgetZariski Λ X) U) where
  obj n := Functor.Fiber.mk (a := standardAffine Λ X n U) sorry
  map f := ⟨standardAffineHom Λ X f U, sorry⟩
  map_id := sorry
  map_comp := sorry

/-- Including `standardCosimplicial U` into `C_{X/Λ}` recovers `standardAffine`. -/
theorem standardCosimplicial_obj (Λ : CommRingCat.{u}) (X : Scheme.{u})
    [X.Over (Spec Λ)] (n : SimplexCategory) (U : X.smallZariskiSite) :
    Functor.Fiber.fiberInclusion.obj ((standardCosimplicial Λ X U).obj n) =
      standardAffine Λ X n U :=
  sorry

/-- The fibrewise standard cosimplicial object, viewed in `C_{X/Λ}`. -/
def standardCosimplicialObj (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (U : X.smallZariskiSite) : CosimplicialObject (Obj Λ X) :=
  standardCosimplicial Λ X U ⋙ Functor.Fiber.fiberInclusion

/-- Degreewise, `standardCosimplicialObj U` is `standardAffine`. -/
theorem standardCosimplicialObj_obj (Λ : CommRingCat.{u}) (X : Scheme.{u})
    [X.Over (Spec Λ)] (n : SimplexCategory) (U : X.smallZariskiSite) :
    (standardCosimplicialObj Λ X U).obj n = standardAffine Λ X n U :=
  sorry

/-- The construction `U ↦ A_{•,U}` as a covariant functor on the small Zariski site. -/
def standardFunctor (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    X.smallZariskiSite ⥤ CosimplicialObject (Obj Λ X) where
  obj U := standardCosimplicialObj Λ X U
  map f :=
    { app n := standardAffineRestrict Λ X f n
      naturality := fun {_ _} _ ↦ sorry }
  map_id := sorry
  map_comp := sorry

/-- Evaluating `standardFunctor` at `U` recovers `standardCosimplicialObj U`. -/
theorem standardFunctor_obj (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (U : X.smallZariskiSite) :
    (standardFunctor Λ X).obj U = standardCosimplicialObj Λ X U :=
  sorry

end AlgebraicGeometry.Scheme.CotangentSite
