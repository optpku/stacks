module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Support

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 59.79.5 (1): Zariski and small-étale global cohomology with support
agree for a quasi-coherent module, without a retrocompactness assumption. -/
@[stacks 0A46] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.cohomologyWithSupport_isomorphic_smallEtale :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      (F : X.Modules) [F.IsQuasicoherent] (q : ℕ)
      [HasSheafify (SmallStandardTopology.etale.topology X) AddCommGrpCat.{u}]
      [(SmallStandardTopology.etale.topology X).WEqualsLocallyBijective AddCommGrpCat.{u}],
      IsIsomorphic
        ((forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat.{u}).obj
          (Scheme.Modules.Support.cohomology (closedImmersionComplement i).compl F q))
        ((forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat.{u}).obj
          (Scheme.Etale.Module.Support.cohomology (closedImmersionComplement i).compl
            (Scheme.AssociatedModule.small .etale X F) q)))

/- Lemma 59.79.5 (2): étale local cohomology is quasi-coherent when the
open complement of the support is retrocompact. -/
@[stacks 0A46] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.smallEtaleCohomologySheafWithSupport_isQuasicoherent :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      (F : X.Modules) [F.IsQuasicoherent] (q : ℕ)
      [HasSheafify (SmallStandardTopology.etale.topology X) AddCommGrpCat.{u}]
      [(SmallStandardTopology.etale.topology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
      [Fact (IsRetrocompact ((closedImmersionComplement i).compl.compl : Set X))],
      (Scheme.Etale.Module.Support.cohomologySheaf (closedImmersionComplement i).compl
        (Scheme.AssociatedModule.small .etale X F) q).IsQuasicoherent)

/- Lemma 59.79.5 (3): with retrocompact complement, étale local cohomology
is the module sheaf associated to Zariski local cohomology. -/
@[stacks 0A46] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.cohomologySheafWithSupport_isomorphic_smallEtale :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      (F : X.Modules) [F.IsQuasicoherent] (q : ℕ)
      [HasSheafify (SmallStandardTopology.etale.topology X) AddCommGrpCat.{u}]
      [(SmallStandardTopology.etale.topology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
      [Fact (IsRetrocompact ((closedImmersionComplement i).compl.compl : Set X))],
      IsIsomorphic
        (Scheme.Etale.Module.Support.cohomologySheaf (closedImmersionComplement i).compl
          (Scheme.AssociatedModule.small .etale X F) q)
        (Scheme.AssociatedModule.small .etale X (Scheme.Modules.Support.cohomologySheaf
          (closedImmersionComplement i).compl F q)))
