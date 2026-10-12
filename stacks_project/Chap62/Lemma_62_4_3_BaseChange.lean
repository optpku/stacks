/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup.Specialization.BaseChange

/-!
# Field-extension base change of generic and special fibres

The fibre and cycle base-change API is exported from its mathematical owners.
The fibre structure morphism is locally of finite type whenever the ambient
morphism is locally of finite type.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

#check (AlgebraicGeometry.Scheme.Hom.instLocallyOfFiniteType_fiberToSpecResidueField :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (s : S),
    LocallyOfFiniteType (f.fiberToSpecResidueField s))
