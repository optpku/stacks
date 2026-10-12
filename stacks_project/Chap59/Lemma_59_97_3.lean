/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Definition_59_31_3_EtaleSupport
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Topology.JacobsonSpace
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

section

variable {X : Scheme.{u}}
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}] [HasTerminal X.Etale]

/-- An abelian sheaf on the small étale site is globally generated if the counit of
the constant-sheaf adjunction at a terminal object is an epimorphism. -/
abbrev IsGloballyGenerated (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) : Prop :=
  Epi ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} terminalIsTerminal).counit.app F)

/-- Global generation of an abelian étale sheaf is the epimorphism condition on the
constant-sheaf adjunction counit. -/
theorem isGloballyGenerated_iff (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    IsGloballyGenerated F ↔
      Epi ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u}
          terminalIsTerminal).counit.app F) := sorry

end

/-- Lemma 59.97.3 (1): if `K` is a separably closed field, `X` is a scheme of finite
type over `K`, and `F` is an abelian sheaf on `X.left.smallEtaleTopology` with
`abelianSheafSupport F ⊆ closedPoints X.left`, then
`IsZero ((Sheaf.functorH X.left.smallEtaleTopology q).obj F)` for every `q > 0`. -/
@[stacks 0F1F]
theorem etaleCohomology_isZero_of_support_closedPoints
    {K : Type u} [Field K] [IsSepClosed K] (X : SchemeOverField K) [Algebraic X]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (hsupp : abelianSheafSupport F ⊆ closedPoints X.left) (q : ℕ) (hq : 0 < q) :
    IsZero ((Sheaf.functorH X.left.smallEtaleTopology q).obj F) := sorry

/-- Lemma 59.97.3 (2): if `K` is a separably closed field, `X` is a scheme of finite
type over `K`, and `F` is an abelian sheaf on `X.left.smallEtaleTopology` with
`abelianSheafSupport F ⊆ closedPoints X.left`, then `F` is globally generated. -/
@[stacks 0F1F]
theorem isGloballyGenerated_of_support_closedPoints
    {K : Type u} [Field K] [IsSepClosed K] (X : SchemeOverField K) [Algebraic X]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasTerminal X.left.Etale]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (hsupp : abelianSheafSupport F ⊆ closedPoints X.left) :
    IsGloballyGenerated F := sorry

end AlgebraicGeometry.Scheme.Etale

end
