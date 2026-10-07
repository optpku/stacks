module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import stacks_project.Chap66.Lemma_66_29_4_Stalk

/-!
# Étale-site support of an 𝒪_X-module

The support of an `𝒪_X`-module on an algebraic space is the set of points of `|X|`
at which an étale module stalk is a nonzero object of `ModuleCat`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

namespace Modules

/-- The étale-site support of an `𝒪_X`-module, as the points of `|X|` admitting a geometric
point whose étale module stalk is a nonzero object of `ModuleCat`. -/
def moduleSupport (F : X.Modules) : Set (Points X) :=
  {x | ∃ xbar : GeometricPoint X, xbar.image = x ∧ ¬ IsZero (stalkModuleCat xbar F)}

/-- Membership in the étale-site support of an `𝒪_X`-module is existence of a geometric point
over the point at which the étale module stalk is nonzero. -/
theorem mem_moduleSupport_iff (F : X.Modules) (x : Points X) :
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

end Modules

end AlgebraicGeometry.AlgebraicSpace
