module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Covering
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Submersive

/-!
# Universal submersiveness of valuative covering families

A valuative covering family induces a universally submersive morphism from
the coproduct of its source schemes to its target.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- The coproduct morphism associated to a `V`-covering family is universally
submersive. -/
@[stacks 0ETP]
theorem universallySubmersive_sigmaDesc_of_isVCovering
    {ι : Type v} {X : Scheme.{u}} [Small.{u} ι]
    (Xi : ι → Scheme.{u}) (f : ∀ i, Xi i ⟶ X)
    (h : IsVCovering X Xi f) :
    UniversallySubmersive (Limits.Sigma.desc f) := sorry

end AlgebraicGeometry
