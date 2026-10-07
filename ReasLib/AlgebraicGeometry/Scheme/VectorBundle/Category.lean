module

public import Mathlib.CategoryTheory.Category.Cat
public import ReasLib.AlgebraicGeometry.Scheme.Cone.Category
public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.Graded

/-!
# Explicit category data for graded vector bundles

Identity and composition are inherited from the underlying cone morphisms and are packaged as
an explicit category value without registering a category instance on vector bundles.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

namespace VectorBundleHom

/-- The identity scheme morphism of a vector bundle lies over the base. -/
theorem idOverBase (E : VectorBundleOver S) :
    (𝟙 E.V) ≫ E.π = E.π := by
  exact ConeHom.idOverBase S E.cone

/-- The identity scheme morphism preserves the grading of the underlying cone. -/
theorem idCompatibleWithGrading (E : VectorBundleOver S) :
    vectorBundleHomCompatibleWithGrading S (𝟙 E.V) (idOverBase S E) := by
  exact ConeHom.idCompatibleWithGrading S E.cone

/-- The identity morphism of a vector bundle. -/
def id (E : VectorBundleOver S) : VectorBundleHom S E E :=
  ConeHom.id S E.cone

/-- The composite of two underlying scheme morphisms lies over the base. -/
theorem compOverBase {E E' E'' : VectorBundleOver S}
    (f : VectorBundleHom S E E') (g : VectorBundleHom S E' E'') :
    (f.hom ≫ g.hom) ≫ E''.π = E.π := by
  exact ConeHom.compOverBase S f g

/-- The composite of two vector-bundle morphisms preserves the grading of the underlying
cones. -/
theorem compCompatibleWithGrading {E E' E'' : VectorBundleOver S}
    (f : VectorBundleHom S E E') (g : VectorBundleHom S E' E'') :
    vectorBundleHomCompatibleWithGrading S (f.hom ≫ g.hom) (compOverBase S f g) := by
  exact ConeHom.compCompatibleWithGrading S f g

/-- Composition of vector-bundle morphisms. -/
def comp {E E' E'' : VectorBundleOver S}
    (f : VectorBundleHom S E E') (g : VectorBundleHom S E' E'') :
    VectorBundleHom S E E'' :=
  ConeHom.comp S f g

/-- Left identity for vector-bundle morphisms. -/
theorem id_comp {E E' : VectorBundleOver S} (f : VectorBundleHom S E E') :
    comp S (id S E) f = f := by
  exact ConeHom.id_comp S f

/-- Right identity for vector-bundle morphisms. -/
theorem comp_id {E E' : VectorBundleOver S} (f : VectorBundleHom S E E') :
    comp S f (id S E') = f := by
  exact ConeHom.comp_id S f

/-- Associativity of vector-bundle morphism composition. -/
theorem assoc {E E' E'' E''' : VectorBundleOver S}
    (f : VectorBundleHom S E E') (g : VectorBundleHom S E' E'')
    (h : VectorBundleHom S E'' E''') :
    comp S (comp S f g) h = comp S f (comp S g h) := by
  exact ConeHom.assoc S f g h

end VectorBundleHom

/-- The category structure carried explicitly by vector bundles over `S`. -/
@[reducible]
def vectorBundleCategory : Category (VectorBundleOver S) where
  Hom E E' := VectorBundleHom S E E'
  id := VectorBundleHom.id S
  comp f g := VectorBundleHom.comp S f g
  id_comp := VectorBundleHom.id_comp S
  comp_id := VectorBundleHom.comp_id S
  assoc := VectorBundleHom.assoc S

/-- The bundled category of vector bundles over `S`. -/
def vectorBundleCat : Cat :=
  ⟨VectorBundleOver S, vectorBundleCategory S⟩

end AlgebraicGeometry.Scheme
