/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Truncation
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open DerivedCategory.TStructure
open scoped DerivedExt

noncomputable section

universe u

/- Lemma 36.40.3: for a perfect derived module `P` on a quasi-compact quasi-separated
scheme, eventual vanishing of `Ext⁽i⁾(P, E)` is equivalent to eventual vanishing after
applying the lower truncation `t.truncGE a` to `E`. -/
@[stacks 0GEL] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.extSubsingletonEventually_iff_truncGE :
    ∀ {X : AlgebraicGeometry.Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    {P : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace},
    AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect P →
    ∀ (E : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent X) (a : ℤ),
      (∀ᶠ i : ℤ in Filter.atTop, Subsingleton (Ext⁽i⁾(P, E.obj))) ↔
      ∀ᶠ i : ℤ in Filter.atTop,
        Subsingleton (Ext⁽i⁾(P, (t.truncGE a).obj E.obj)))
