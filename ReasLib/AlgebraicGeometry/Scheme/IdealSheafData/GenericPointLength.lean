/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Length
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Dimension
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
public import ReasLib.Topology.Specialization.Dimension

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- At a generic point of an irreducible component of a closed subscheme of a locally
Noetherian scheme, the subscheme stalk has finite length as a module over the ambient stalk. -/
theorem stalk_length_lt_top_at_genericPoint
    {X : Scheme.{u}} [IsLocallyNoetherian X] (Z : X.IdealSheafData)
    (ξ : genericPoints Z.subscheme) :
    let 𝒪Z := Z.subscheme.presheaf
    Module.length (X.presheaf.stalk (Z.subschemeι ξ.1))
      ((ModuleCat.restrictScalars (Z.subschemeι.stalkMap ξ.1).hom).obj
        (ModuleCat.of (𝒪Z.stalk ξ.1) (𝒪Z.stalk ξ.1))) < ⊤ := sorry

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.Hom

/-- At a generic point of an irreducible component of a closed subscheme locally of finite type
over a universally catenary scheme, the subscheme stalk has finite length as a module over the
ambient stalk. -/
theorem closedSubschemeStalk_length_lt_top_at_genericPoint
    {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (Z : X.IdealSheafData)
    (ξ : genericPoints Z.subscheme) :
    let 𝒪Z := Z.subscheme.presheaf
    Module.length (X.presheaf.stalk (Z.subschemeι ξ.1))
      ((ModuleCat.restrictScalars (Z.subschemeι.stalkMap ξ.1).hom).obj
        (ModuleCat.of (𝒪Z.stalk ξ.1) (𝒪Z.stalk ξ.1))) < ⊤ := sorry

end AlgebraicGeometry.Scheme.Hom
