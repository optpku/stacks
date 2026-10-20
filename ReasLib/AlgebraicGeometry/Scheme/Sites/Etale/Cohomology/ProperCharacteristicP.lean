module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Constant
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.Small

/-- Constant `ZMod p` étale cohomology of a proper scheme over an algebraically
closed field of positive characteristic `p` is finite in every degree. -/
instance constantZModCohomology_finite_of_isProper
    {k : Type u} [Field k] [IsAlgClosed k] {p : ℕ} [CharP k p]
    [Fact (0 < p)] (X : SchemeOverField k) [IsProper X.hom]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (q : ℕ) : Finite (constantZModCohomology X.left p q) := sorry

/-- Pullback along an algebraically closed field extension is an isomorphism on
constant `ZMod p` étale cohomology of a proper scheme in characteristic `p > 0`. -/
instance constantZModCohomologyPullback_isIso_of_isProper
    {k k' : Type u} [Field k] [IsAlgClosed k] {p : ℕ} [CharP k p]
    [Fact (0 < p)] (X : SchemeOverField k) [IsProper X.hom]
    [Field k'] [IsAlgClosed k'] [Algebra k k']
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasSheafify (FieldExtension.Over.baseChange k k' X).left.smallEtaleTopology
      AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (FieldExtension.Over.baseChange k k' X).left.smallEtaleTopology
      AddCommGrpCat.{u + 1})]
    (q : ℕ) :
    IsIso (constantZModCohomologyPullback (FieldExtension.Over.toSource k k' X) p q) := sorry

end AlgebraicGeometry.Scheme.Etale.Small
