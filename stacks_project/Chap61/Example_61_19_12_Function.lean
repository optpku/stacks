module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Function sheaves on the small pro-étale site

The abelian sheaf of all point-set maps into an abelian group, the comparison
from the constant sheaf, and the sheaf cokernel of that comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.ProEt

/-- Precomposition of point-set function groups along a map of index types. -/
def functionMap {A : Type u} [AddCommGroup A] {X : Type v} {Y : Type w} (φ : Y → X) :
    (X → A) →+ (Y → A) :=
  AddMonoidHom.pi fun y ↦ Pi.evalAddMonoidHom (fun _ ↦ A) (φ y)

/-- Evaluating a precomposition map at a point recovers ordinary composition. -/
theorem functionMap_apply {A : Type u} [AddCommGroup A] {X : Type v} {Y : Type w}
    (φ : Y → X) (g : X → A) (y : Y) :
    functionMap φ g y = g (φ y) :=
  sorry

/-- The presheaf on `X.ProEt` sending `U` to the abelian group of all maps of
points `U.left → A`. -/
def functionPresheaf (X : Scheme.{u}) (A : Type (u + 1)) [AddCommGroup A] :
    X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj U := AddCommGrpCat.of (U.unop.left → A)
  map f := AddCommGrpCat.ofHom (functionMap (f.unop.left : _ → _))
  map_id := sorry
  map_comp := sorry

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
  sorry

/-- The presheaf morphism sending a coefficient to the corresponding constant
function. -/
def constantToFunctionPresheaf (X : Scheme.{u}) (A : Type (u + 1)) [AddCommGroup A] :
    (Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of A) ⟶ functionPresheaf X A where
  app U := AddCommGrpCat.ofHom (Pi.constAddMonoidHom U.unop.left A)
  naturality := sorry

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

end AlgebraicGeometry.Scheme.ProEt
