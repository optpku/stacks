/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Support
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.Complement

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- Zariski and small-étale global cohomology with closed support agree for
a quasi-coherent module. -/
theorem cohomologyWithSupport_isomorphic_smallEtale
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : X.Modules) [F.IsQuasicoherent] (q : ℕ)
    [HasSheafify (SmallStandardTopology.etale.topology X) AddCommGrpCat.{u}]
    [(SmallStandardTopology.etale.topology X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    IsIsomorphic
      ((forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat.{u}).obj
        (Modules.Support.cohomology (closedImmersionComplement i).compl F q))
      ((forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat.{u}).obj
        (Etale.Module.Support.cohomology (closedImmersionComplement i).compl
          (small .etale X F) q)) := sorry

/-- With retrocompact open complement, étale local cohomology of an associated
quasi-coherent module is isomorphic to the associated Zariski local-cohomology module. -/
theorem cohomologySheafWithSupport_isomorphic_smallEtale
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : X.Modules) [F.IsQuasicoherent] (q : ℕ)
    [HasSheafify (SmallStandardTopology.etale.topology X) AddCommGrpCat.{u}]
    [(SmallStandardTopology.etale.topology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [Fact (IsRetrocompact ((closedImmersionComplement i).compl.compl : Set X))] :
    IsIsomorphic
      (Etale.Module.Support.cohomologySheaf (closedImmersionComplement i).compl
        (small .etale X F) q)
      (small .etale X (Modules.Support.cohomologySheaf
        (closedImmersionComplement i).compl F q)) := sorry

/-- Étale local cohomology of an associated quasi-coherent module is quasi-coherent
when the open complement of the closed support is retrocompact. -/
instance smallEtaleCohomologySheafWithSupport_isQuasicoherent
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : X.Modules) [F.IsQuasicoherent] (q : ℕ)
    [HasSheafify (SmallStandardTopology.etale.topology X) AddCommGrpCat.{u}]
    [(SmallStandardTopology.etale.topology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [Fact (IsRetrocompact ((closedImmersionComplement i).compl.compl : Set X))] :
    (Etale.Module.Support.cohomologySheaf (closedImmersionComplement i).compl
      (small .etale X F) q).IsQuasicoherent := sorry

end AlgebraicGeometry.Scheme.AssociatedModule
