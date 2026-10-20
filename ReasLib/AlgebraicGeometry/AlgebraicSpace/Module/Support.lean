module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Stalk

/-!
# Support of module sheaves on algebraic spaces

The support of a module sheaf is the support of its underlying abelian sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The support of an `𝒪_X`-module is the support of its underlying abelian sheaf on the small
étale site. -/
abbrev moduleSupport (F : X.Modules) : Set (Points X) :=
  abelianSheafSupport ((SheafOfModules.toSheaf (structureSheaf X)).obj F)

/-- Membership in the support of an `𝒪_X`-module is existence of a geometric point over the
point at which the geometric stalk of the underlying abelian sheaf is nonzero. -/
theorem mem_moduleSupport_iff (F : X.Modules) (x : Points X) :
    x ∈ moduleSupport F ↔
      ∃ xbar : GeometricPoint X, xbar.image = x ∧
        ¬ IsZero (abelianGeometricStalk
            ((SheafOfModules.toSheaf (structureSheaf X)).obj F) xbar) := by
  exact mem_abelianSheafSupport_iff
    ((SheafOfModules.toSheaf (structureSheaf X)).obj F) x

/-- Membership in the support of an `𝒪_X`-module is existence of a geometric point
over the point at which the étale module stalk is nonzero. -/
theorem mem_moduleSupport_iff_moduleStalk (F : X.Modules) (x : Points X) :
    x ∈ moduleSupport F ↔
      ∃ xbar : GeometricPoint X, xbar.image = x ∧ ¬ IsZero (stalkModuleCat xbar F) :=
  sorry

/-- Whether the étale module stalk is zero depends only on the image point in `|X|`. -/
theorem moduleSupport_isZero_iff_of_image_eq (F : X.Modules) (xbar tbar : GeometricPoint X)
    (himage : xbar.image = tbar.image) :
    IsZero (stalkModuleCat xbar F) ↔ IsZero (stalkModuleCat tbar F) :=
  sorry

/-- For any geometric point, support membership of its image is equivalent to nonvanishing of
its étale module stalk. -/
theorem mem_moduleSupport_iff_stalk (F : X.Modules) (xbar : GeometricPoint X) :
    xbar.image ∈ moduleSupport F ↔ ¬ IsZero (stalkModuleCat xbar F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
