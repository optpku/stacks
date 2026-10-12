/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ext
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree

/-!
# Ext and finite locally free tensor factors

Finite locally free tensor factors move across sheaf and global Ext by internal-Hom duality.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Ext

/-- Tensoring the first argument of sheaf Ext by a finite locally free module is equivalent
to tensoring its second argument by the internal-Hom dual. -/
theorem sheafExt_tensor {X : RingedSpace.{u}}
    (E F G : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ) :
    IsIsomorphic (sheafExt (F ⊗ E) G i)
      (sheafExt F (((ihom E).obj (SheafOfModules.unit X.ringCatSheaf)) ⊗ G) i) := sorry

/-- Sheaf Ext commutes with tensoring its second argument by the dual of a finite locally
free module. -/
theorem sheafExt_tensorDual {X : RingedSpace.{u}}
    (E F G : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ) :
    IsIsomorphic (sheafExt F (((ihom E).obj (SheafOfModules.unit X.ringCatSheaf)) ⊗ G) i)
      (sheafExt F G i ⊗ ((ihom E).obj (SheafOfModules.unit X.ringCatSheaf))) := sorry

/-- Tensoring the first argument of global Ext by a finite locally free module is equivalent
to tensoring its second argument by the internal-Hom dual. -/
theorem ext_tensor {X : RingedSpace.{u}}
    (E F G : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ) :
    IsIsomorphic (AddCommGrpCat.of (Abelian.Ext (F ⊗ E) G i))
      (AddCommGrpCat.of
        (Abelian.Ext F (((ihom E).obj (SheafOfModules.unit X.ringCatSheaf)) ⊗ G) i)) := sorry

/-- Global Ext from a finite locally free module is cohomology of its internal-Hom dual
tensored with the target module. -/
theorem ext_eq_cohomology {X : RingedSpace.{u}}
    (E G : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ) :
    IsIsomorphic (AddCommGrpCat.of (Abelian.Ext E G i))
      (AlgebraicGeometry.RingedSpace.moduleCohomology
        (((ihom E).obj (SheafOfModules.unit X.ringCatSheaf)) ⊗ G) i) := sorry

end AlgebraicGeometry.RingedSpace.Ext
