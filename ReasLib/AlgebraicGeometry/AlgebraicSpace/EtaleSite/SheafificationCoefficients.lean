/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Lean.Util.CollectAxioms

/-! # Proved upper-universe sheafification certificates

These generic certificates are built before importing the specialized space
instances. They use Mathlib's plus construction, not an admitted right adjoint.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PullbackFactory.CoefficientSheafification

theorem additive {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) :
    HasSheafify J AddCommGrpCat.{u + 1} := by
  infer_instance

theorem commRing {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) :
    HasSheafify J CommRingCat.{u + 1} := by
  infer_instance

theorem additiveW {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) :
    J.WEqualsLocallyBijective AddCommGrpCat.{u + 1} := by
  infer_instance

theorem commRingW {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) :
    J.WEqualsLocallyBijective CommRingCat.{u + 1} := by
  infer_instance

run_cmd do
  for n in [``additive, ``commRing, ``additiveW, ``commRingW] do
    let axs ← Lean.Elab.Command.liftCoreM (Lean.collectAxioms n)
    unless axs.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Uncertified sheafification: {n}: {axs}"
    Lean.logInfo m!"CLEAN_SHEAFIFICATION|{n}|{axs}"

end AlgebraicGeometry.AlgebraicSpace.PullbackFactory.CoefficientSheafification
