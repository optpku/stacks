/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Topology.LocallyConstant.Basic
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.StalkwiseFree

/-!
# Fibers and fiber ranks of module sheaves

The fiber of a module sheaf at a point of a locally ringed space is the tensor product of its
stalk with the residue field.  This leaf gives that object and its two standard rank values
names, keeping later local-freeness criteria free of repeated tensor-product expressions.
-/

@[expose] public section

open AlgebraicGeometry
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.Modules

variable {X : LocallyRingedSpace.{u}}

/-- The underlying carrier of the stalk of a module sheaf at a point of a locally ringed space.
The canonical module action is supplied by `RingedSpace.moduleStalkModule`. -/
noncomputable abbrev stalk (ℱ : X.Modules) (x : X) : Type u :=
  TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ℱ.val.presheaf x

/-- A stalkwise-free module sheaf has a free underlying stalk carrier at each point of its
underlying locally ringed space. -/
instance instModuleFreeStalkOfIsStalkwiseFree
    {ℱ : X.Modules}
    [RingedSpace.Modules.IsStalkwiseFree (X := X.toRingedSpace) ℱ] (x : X) :
    Module.Free (X.presheaf.stalk x) (stalk ℱ x) := sorry

/-- The fiber `κ(x) ⊗[𝒪_{X,x}] ℱ_x` of a module sheaf at a point of a locally ringed space. -/
abbrev fiber (ℱ : X.Modules) (x : X) : Type u :=
  IsLocalRing.ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x]
    (stalk ℱ x)

/-- The finite rank of the fiber of a module sheaf at a point. -/
noncomputable def fiberFinrank (ℱ : X.Modules) (x : X) : ℕ :=
  Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x)) (fiber ℱ x)

/-- The integer-valued fiber-rank function used in local-constancy statements. -/
noncomputable def fiberRank (ℱ : X.Modules) (x : X) : ℤ :=
  (fiberFinrank ℱ x : ℤ)

/-- The integer-valued fiber rank is the coercion of the natural-valued fiber finite rank. -/
@[simp]
theorem fiberRank_eq_intCast_fiberFinrank (ℱ : X.Modules) (x : X) :
    fiberRank ℱ x = (fiberFinrank ℱ x : ℤ) := sorry

/-- A module sheaf has locally constant fiber rank when its integer-valued fiber-rank function
is locally constant on the underlying topological space. -/
class IsFiberRankLocallyConstant (ℱ : X.Modules) : Prop where
  /-- Local constancy of the fiber-rank function. -/
  fiber_rank_locallyConstant : IsLocallyConstant (fiberRank ℱ)

/-- The bundled fiber-rank condition is equivalent to local constancy of its named rank
function. -/
theorem isFiberRankLocallyConstant_iff (ℱ : X.Modules) :
    IsFiberRankLocallyConstant ℱ ↔ IsLocallyConstant (fiberRank ℱ) := sorry

end AlgebraicGeometry.LocallyRingedSpace.Modules
