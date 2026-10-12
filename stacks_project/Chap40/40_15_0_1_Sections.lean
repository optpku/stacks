/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaf.CompactOpen.Intersection

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe w

namespace TopCat.Sheaf.CompactOpen.Intersection

variable {C : Type (w + 1)} [Category.{w} C]
variable {FC : C → C → Type w} {CC : C → Type w}
variable [∀ P Q, FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{w} C FC]
variable [HasColimits C] [HasLimits C]
variable [PreservesLimits (CategoryTheory.forget C)]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable {X : TopCat.{w}} [T0Space X] [QuasiSober X] [PrespectralSpace X]
variable [QuasiSeparatedSpace X] {W : Set X} {S : Set (CompactOpens X)}
variable (h : IsCompactOpenDirectedIntersection W S) (F : X.Sheaf C)

#check (TopCat.Sheaf.CompactOpen.Intersection.comparison_isIso h F :
  IsIso (TopCat.Sheaf.CompactOpen.Intersection.comparison h F))

end TopCat.Sheaf.CompactOpen.Intersection
