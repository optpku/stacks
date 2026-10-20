module

public import ReasLib.Topology.Sheaves.Basis.Algebraic.Restriction
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits TopologicalSpace

universe u v w u1

variable {X : TopCat.{u}}
variable {C : Type v} [Category.{w} C]
variable {F : C ⥤ Type u1} [IsAlgebraicStructure C F]
variable {B : Set (Opens X)}
variable [HasLimitsOfSize.{u, u} C] [PreservesLimitsOfSize.{u, u} F]
variable (hB : Opens.IsBasis B)

/- Lemma 6.30.10: restriction from `C`-valued sheaves on `X` to sheaves with values in the fixed
type of algebraic structure `(C, F)` on the topological basis `B` is an equivalence. -/
@[stacks 009R]
#check (AlgebraicBasisSheaf.restriction_isEquivalence (F := F) hB)
