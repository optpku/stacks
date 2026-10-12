/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaves.Basis.Algebraic.Extension
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits TopologicalSpace

universe u v w u1

variable {X : TopCat.{u}} {C : Type v} [Category.{w} C]
variable {F : C ⥤ Type u1} [IsAlgebraicStructure C F]
variable {B : Set (Opens X)}
variable [HasLimitsOfSize.{u, u} C] [PreservesLimitsOfSize.{u, u} F]
variable (ℱ : AlgebraicBasisSheaf F B) (hB : Opens.IsBasis B)

/- Lemma 6.30.9: a sheaf with values in a type of algebraic structure on a topological basis
extends to a sheaf on the whole space, uniquely up to a unique isomorphism compatible with its
values and restriction maps on basis opens. -/
@[stacks 009Q]
#check AlgebraicBasisSheaf.existsExtensionUniqueUpToUniqueIso ℱ hB
