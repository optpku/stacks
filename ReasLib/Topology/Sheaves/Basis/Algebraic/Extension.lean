/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sheaves.Sheaf
public import ReasLib.Topology.Sheaves.Basis.Algebraic.Comparison
public import ReasLib.Topology.Sheaves.Basis.Extension

/-!
# Extension of algebraic sheaves from a topological basis

Concrete extension data is owned by `BasisSiteSheaf.extend`.  This module records the invariant
existence-and-uniqueness statement for the source-style algebraic basis-sheaf predicate.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace

universe u v w u1

variable {X : TopCat.{u}}
variable {C : Type v} [Category.{w} C]
variable {F : C ⥤ Type u1} [IsAlgebraicStructure C F]
variable {B : Set (Opens X)}
variable [HasLimitsOfSize.{u, u} C] [PreservesLimitsOfSize.{u, u} F]

namespace AlgebraicBasisSheaf

/-- A sheaf with values in a type of algebraic structure on a topological basis
extends to a sheaf on the whole space, uniquely up to a unique isomorphism compatible with its
values and restriction maps on basis opens. -/
theorem existsExtensionUniqueUpToUniqueIso (ℱ : AlgebraicBasisSheaf F B)
    (hB : Opens.IsBasis B) :
    ∃ E : BasisPresheaf.Extension ℱ.obj,
      ∀ G : BasisPresheaf.Extension ℱ.obj,
        ∃! e : E.sheaf ≅ G.sheaf, BasisPresheaf.Extension.IsCompatibleIso E G e := sorry

end AlgebraicBasisSheaf
