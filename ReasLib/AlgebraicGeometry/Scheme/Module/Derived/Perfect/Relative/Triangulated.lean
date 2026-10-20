module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent.Triangulated
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Triangulated

@[expose] public section

/-!
# Triangles of relatively perfect derived modules on schemes

Relative perfectness for flat, locally finitely presented scheme morphisms is closed under
the triangulated structure on derived modules.
-/

open CategoryTheory

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.Scheme.ModuleDerived

variable {X S : Scheme.{u}}

/-- The objects perfect relative to a flat, locally finitely presented scheme morphism form
a triangulated object property. -/
instance perfectRelativeTo_isTriangulated (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))] :
    ObjectProperty.IsTriangulated (perfectRelativeTo f) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
