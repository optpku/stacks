/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Additive
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Stalk
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalk complexes of modules on a ringed site

Taking the module-valued stalk at a point is additive, hence acts degreewise on cochain
complexes. This file owns that functorial data independently of properties of complexes.
-/

@[expose] public section

open CategoryTheory
open ComplexShape
open SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The degreewise module-stalk functor on unbounded cochain complexes. -/
@[stacks 0DEN "stalk complex"]
noncomputable abbrev moduleStalkComplex
    (p : Point.{w} J) (O : Sheaf J CommRingCat.{w}) :
    CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ ⥤
      CochainComplex (ModuleCat.{w} (p.stalkCommRing O)) ℤ :=
  (p.moduleStalkFunctor O).mapHomologicalComplex (up ℤ)

namespace moduleStalkComplex

/-- In each degree, the module-stalk complex is the stalk of the corresponding term. -/
@[simp]
theorem obj_X
    (p : Point.{w} J) (O : Sheaf J CommRingCat.{w})
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ) (n : ℤ) :
    ((p.moduleStalkComplex O).obj K).X n = p.moduleStalk O (K.X n) := sorry

end moduleStalkComplex
end CategoryTheory.GrothendieckTopology.Point
