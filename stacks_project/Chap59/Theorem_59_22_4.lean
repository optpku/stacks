module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Cohomology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

/- Theorem 59.22.4 (1): scheme cohomology of a quasi-coherent module agrees with
cohomology of its associated additive sheaf on each of the five standard big sites. -/
@[stacks 03P2] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.cohomology_isomorphic_big :
    ∀ (τ : StandardTopology) (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]
      (q : ℕ) [HasSheafify (τ.overTopology S) AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf (τ.overTopology S) AddCommGrpCat.{u})],
      IsIsomorphic
        ((forget₂ (ModuleCat Γ(S, ⊤)) AddCommGrpCat.{u}).obj
          (Scheme.Modules.cohomology F q))
        ((Sheaf.functorH (τ.overTopology S) q).obj
          ((SheafOfModules.toSheaf (Scheme.AssociatedModule.bigStructureSheaf τ S)).obj
            (Scheme.AssociatedModule.big τ S F))))

/- Theorem 59.22.4 (2): scheme cohomology of a quasi-coherent module agrees with
cohomology of its associated additive sheaf on the small etale site. -/
@[stacks 03P2] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.cohomology_isomorphic_small .etale :
    ∀ (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]
      (q : ℕ) [HasSheafify (SmallStandardTopology.etale.topology S) AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf (SmallStandardTopology.etale.topology S) AddCommGrpCat.{u})],
      IsIsomorphic
        ((forget₂ (ModuleCat Γ(S, ⊤)) AddCommGrpCat.{u}).obj
          (Scheme.Modules.cohomology F q))
        ((Sheaf.functorH (SmallStandardTopology.etale.topology S) q).obj
          ((SheafOfModules.toSheaf (Scheme.AssociatedModule.smallStructureSheaf .etale S)).obj
            (Scheme.AssociatedModule.small .etale S F))))
