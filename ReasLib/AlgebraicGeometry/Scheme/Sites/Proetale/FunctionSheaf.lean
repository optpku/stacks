module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.WeaklyEtale.Point
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleComparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Cohomology.ZeroDimensional

/-!
# Function sheaves on the small pro-étale site

The abelian sheaf of all point-set maps into an abelian group, the comparison
from the constant sheaf, and the sheaf cokernel of that comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/-- The presheaf on `X.ProEt` sending `U` to the abelian group of all maps of
points `U.left → A`. -/
def functionPresheaf (X : Scheme.{u}) (A : Type (u + 1)) [AddCommGroup A] :
    X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj U := AddCommGrpCat.of (U.unop.left → A)
  map f := AddCommGrpCat.ofHom
    (AddMonoidHom.pi fun y ↦ Pi.evalAddMonoidHom (fun _ ↦ A) (f.unop.left y))
  map_id U := by
    ext g y
    rfl
  map_comp f g := by
    ext h y
    rfl

/-- The function presheaf of all point-set maps is a sheaf for the small
pro-étale topology. -/
theorem functionPresheaf_isSheaf (X : Scheme.{u}) (A : Type (u + 1)) [AddCommGroup A] :
    Presheaf.IsSheaf (topology X) (functionPresheaf X A) :=
  sorry

/-- The abelian sheaf of all point-set maps `U.left → A` on the small pro-étale
site of `X`. -/
def functionSheaf (X : Scheme.{u}) (A : Type (u + 1)) [AddCommGroup A] :
    Sheaf (topology X) AddCommGrpCat.{u + 1} :=
  ⟨functionPresheaf X A, functionPresheaf_isSheaf X A⟩

/-- On an object `U` of `X.ProEt`, the function sheaf evaluates as the group of
all maps of points `U.left → A`. -/
theorem functionSheaf_obj (X : Scheme.{u}) (A : Type (u + 1)) [AddCommGroup A]
    (U : X.ProEt) :
    (functionSheaf X A).obj.obj (op U) = AddCommGrpCat.of (U.left → A) :=
  rfl

/-- The presheaf morphism sending a coefficient to the corresponding constant
function. -/
def constantToFunctionPresheaf (X : Scheme.{u}) (A : Type (u + 1)) [AddCommGroup A] :
    (Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of A) ⟶ functionPresheaf X A where
  app U := AddCommGrpCat.ofHom (Pi.constAddMonoidHom U.unop.left A)
  naturality U V f := by
    ext a
    rfl

/-- The canonical comparison `underline(A) ⟶ fun(-, A)` of sheaves on `X.ProEt`. -/
def constantToFunction (X : Scheme.{u}) (A : Type (u + 1)) [AddCommGroup A]
    [HasSheafify (topology X) AddCommGrpCat.{u + 1}] :
    (constantSheaf (topology X) AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of A) ⟶
      functionSheaf X A :=
  ((sheafificationAdjunction (topology X) AddCommGrpCat.{u + 1}).homEquiv
      ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of A)) (functionSheaf X A)).symm
    (constantToFunctionPresheaf X A)

/-- After the sheafification unit, the comparison is the constant-functions map. -/
theorem constantToFunction_app_eq (X : Scheme.{u}) (A : Type (u + 1)) [AddCommGroup A]
    [HasSheafify (topology X) AddCommGrpCat.{u + 1}] (U : X.ProEt) :
    (toSheafify (topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of A))).app (op U) ≫
        (constantToFunction X A).hom.app (op U) =
      AddCommGrpCat.ofHom (Pi.constAddMonoidHom U.left A) :=
  sorry

/-- The sheaf cokernel `F` of `underline(A) ⟶ fun(-, A)` on `X.ProEt`. -/
def functionsModLocallyConstant (X : Scheme.{u}) (A : Type (u + 1)) [AddCommGroup A]
    [HasSheafify (topology X) AddCommGrpCat.{u + 1}] :
    Sheaf (topology X) AddCommGrpCat.{u + 1} :=
  cokernel (constantToFunction X A)

/-- The short complex `underline(A) ⟶ fun(-, A) ⟶ F` of abelian sheaves on
`X.ProEt`. -/
def functionsModLocallyConstantSequence (X : Scheme.{u}) (A : Type (u + 1))
    [AddCommGroup A] [HasSheafify (topology X) AddCommGrpCat.{u + 1}] :
    ShortComplex (Sheaf (topology X) AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk (constantToFunction X A) (cokernel.π (constantToFunction X A))
    (cokernel.condition (constantToFunction X A))

/-- The canonical sequence from the constant sheaf to the point-function sheaf
and its cokernel is short exact. -/
theorem functionsModLocallyConstantSequence_shortExact
    (X : Scheme.{u}) (A : Type (u + 1)) [AddCommGroup A]
    [HasSheafify (topology X) AddCommGrpCat.{u + 1}] :
    (functionsModLocallyConstantSequence X A).ShortExact :=
  sorry

/-- The inverse image of the constant étale sheaf is isomorphic to the constant
pro-étale sheaf. -/
theorem constantSheaf_etaleToProEtPullback_isIsomorphic
    (X : Scheme.{u}) (A : Type (u + 1)) [AddCommGroup A]
    [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleToProEt X).op.HasLeftKanExtension F]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify (topology X) AddCommGrpCat.{u + 1}] :
    IsIsomorphic
      ((etaleToProEtPullback X AddCommGrpCat.{u + 1}).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of A)))
      ((constantSheaf (topology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of A)) :=
  sorry

/-- On a nonempty scheme, the sheaf of point functions with nontrivial
coefficients does not belong to the essential image of étale inverse image. -/
theorem functionSheaf_not_mem_essImage
    (X : Scheme.{u}) (hX : Nonempty X) (A : Type (u + 1)) [AddCommGroup A] [Nontrivial A]
    [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleToProEt X).op.HasLeftKanExtension F]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify (topology X) AddCommGrpCat.{u + 1}] :
    ¬ (etaleToProEtPullback X AddCommGrpCat.{u + 1}).essImage (functionSheaf X A) :=
  sorry

/-- On a nonempty scheme, the quotient of point functions by locally constant
functions with nontrivial coefficients does not belong to the essential image
of étale inverse image. -/
theorem functionsModLocallyConstant_not_mem_essImage
    (X : Scheme.{u}) (hX : Nonempty X) (A : Type (u + 1)) [AddCommGroup A] [Nontrivial A]
    [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleToProEt X).op.HasLeftKanExtension F]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify (topology X) AddCommGrpCat.{u + 1}] :
    ¬ (etaleToProEtPullback X AddCommGrpCat.{u + 1}).essImage
        (functionsModLocallyConstant X A) :=
  sorry

/-- On an affine pro-étale object over a scheme with closed points and separably
closed residue fields, sections of the quotient sheaf are isomorphic to the
cokernel of the constant-function comparison on sections. -/
theorem functionsModLocallyConstant_sections
    (X : Scheme.{u}) (A : Type (u + 1)) [AddCommGroup A]
    (h_closed : ∀ x : X, IsClosed ({x} : Set X))
    (h_res : ∀ x : X, IsSepClosed (X.residueField x))
    (U : X.ProEt) [IsAffine U.left]
    [HasSheafify (topology X) AddCommGrpCat.{u + 1}] :
    IsIsomorphic ((functionsModLocallyConstant X A).obj.obj (op U))
      (cokernel ((constantToFunction X A).hom.app (op U))) :=
  sorry

end AlgebraicGeometry.Scheme.ProEt
