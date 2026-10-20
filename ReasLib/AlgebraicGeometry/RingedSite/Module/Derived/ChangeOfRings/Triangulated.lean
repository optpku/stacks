/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.Triangulated
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure
import Mathlib.Tactic.CrossRefAttribute

/-!
# Triangulated same-site change of rings

The same-site derived extension of scalars is definitionally a bundled module pullback.  These
bridges keep the pullback triangulation owner visible to typeclass search at the source-facing
`SameSite.pullbackDerived` API.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uX vX uY vY w z

namespace RingedSite.Hom.pullbackOfModel

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
variable {f : RingedSite.Hom X Y}
variable [((f.modulePushforward.{z}).IsRightAdjoint)]

/-- An explicit derived pullback model admits a triangulated-structure proposition.  The model law,
rather than a newly selected total-derived functor, is the input exposed to downstream code. -/
@[stacks 06YY "explicit derived pullback model is triangulated"]
theorem hasTriangulatedStructure (M : PullbackModel f) :
    (pullbackOfModel M).HasTriangulatedStructure := sorry

end RingedSite.Hom.pullbackOfModel

namespace RingedSite.SameSite.pullbackDerived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [UnivLE.{max u v, z}]
variable [HasWeakSheafify J AddCommGrpCat.{z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
variable {O O' : Sheaf J RingCat.{w}}

/-- Same-site derived extension of scalars admits a triangulated-structure proposition at the
generic `RingCat` layer.  The proposition avoids selecting a noncanonical shift comparison while
remaining directly consumable by downstream exact-functor statements. -/
@[stacks 06YY "same-site derived extension is triangulated"]
theorem hasTriangulatedStructure (α : O ⟶ O') :
    (RingedSite.SameSite.pullbackDerived α).HasTriangulatedStructure := sorry

end RingedSite.SameSite.pullbackDerived

namespace SheafOfModules.RingedSite.SameSite.pullbackDerived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O O' : Sheaf J CommRingCat.{w}}
variable [CategoryWithHomology
  (RingedSite.ModuleCat.{w} (RingedSite.ofCommRingSheaf J O))]

/-- The source-facing same-site owner inherits the canonical integer-shift comparison from the
bundled ringed-site pullback. -/
@[stacks 06YY "same-site derived extension shift"]
noncomputable instance commShift (α : O ⟶ O') :
    (SameSite.pullbackDerived α).CommShift ℤ :=
  RingedSite.Hom.modulePullbackDerived.commShift (f := sameSiteHom α)

/-- The same-site derived extension is exact in the triangulated sense. -/
@[stacks 06YY "same-site derived extension is triangulated", instance]
theorem isTriangulated (α : O ⟶ O') :
    (SameSite.pullbackDerived α).IsTriangulated := sorry

end SheafOfModules.RingedSite.SameSite.pullbackDerived
