/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (s : Spec (.of Ω) ⟶ S)

/-- The stalk functor on abelian presheaves on the small étale site at a geometric point
is exact. -/
theorem presheafAbelianStalkExact :
    exactFunctor (S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) AddCommGrpCat.{u}
      (Scheme.pointSmallEtale s).presheafFiber := sorry

/-- The canonical map from a set-valued étale presheaf to its sheafification induces an
isomorphism on the stalk at a geometric point. -/
theorem isIso_stalkMap_toSheafify (F : S.Etaleᵒᵖ ⥤ Type u) :
    IsIso ((Scheme.pointSmallEtale s).presheafFiber.map
      (toSheafify (smallEtaleTopology S) F)) := sorry

/-- The stalk functor on abelian sheaves on the small étale site at a geometric point
is exact. -/
theorem sheafAbelianStalkExact :
    exactFunctor (Sheaf (smallEtaleTopology S) AddCommGrpCat.{u}) AddCommGrpCat.{u}
      (Scheme.pointSmallEtale s).sheafFiber := sorry

/-- The stalk functor on set-valued presheaves on the small étale site at a geometric
point preserves finite limits and finite colimits. -/
theorem presheafTypeStalkExact :
    exactFunctor (S.Etaleᵒᵖ ⥤ Type u) (Type u)
      (Scheme.pointSmallEtale s).presheafFiber := sorry

/-- The stalk functor on set-valued sheaves on the small étale site at a geometric point
preserves finite limits and finite colimits. -/
theorem sheafTypeStalkExact :
    exactFunctor (Sheaf (smallEtaleTopology S) (Type u)) (Type u)
      (Scheme.pointSmallEtale s).sheafFiber := sorry

/-- The stalk functor on set-valued presheaves on the small étale site at a geometric
point preserves all small colimits. -/
theorem presheafTypeStalkPreservesColimits :
    PreservesColimits ((Scheme.pointSmallEtale s).presheafFiber :
      (S.Etaleᵒᵖ ⥤ Type u) ⥤ Type u) := sorry

/-- The stalk functor on set-valued sheaves on the small étale site at a geometric point
preserves all small colimits. -/
theorem sheafTypeStalkPreservesColimits :
    PreservesColimits ((Scheme.pointSmallEtale s).sheafFiber :
      Sheaf (smallEtaleTopology S) (Type u) ⥤ Type u) := sorry

end AlgebraicGeometry.Scheme.Etale
