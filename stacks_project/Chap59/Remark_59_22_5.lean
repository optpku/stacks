module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Cohomology.Objectwise
public import ReasLib.CategoryTheory.Sites.Cohomology.Derived
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Sheaf

noncomputable section

universe u v w

section

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{w})]
variable [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{w})]

/- Remark 59.22.5 (1): Since `S` is a final object, the cohomology groups on the
right-hand side are the right-derived functors of global sections. -/
@[stacks 03P3]
#check (CategoryTheory.Sheaf.rightDerivedGlobalSections_isIsomorphic_functorH J :
  ∀ p : ℕ,
    IsIsomorphic
      ((Γ J AddCommGrpCat.{w}).rightDerived p)
      (CategoryTheory.Sheaf.functorH J p))

end

/- Remark 59.22.5 (2): For any object `f : U ⟶ S` of the site, the cohomology
of the pullback of a quasicoherent module is identified with the objectwise
cohomology of its associated big-site sheaf. -/
@[stacks 03P3]
#check (AlgebraicGeometry.Scheme.AssociatedModule.cohomologyAtObject_isomorphic_big :
  ∀ (τ : StandardTopology) (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]
    (U : Over S) (p : ℕ)
    [HasSheafify (τ.overTopology S) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (τ.overTopology S) AddCommGrpCat.{u})],
    IsIsomorphic
      ((forget₂ (ModuleCat Γ(U.left, ⊤)) AddCommGrpCat.{u}).obj
        (Scheme.Modules.cohomology ((Scheme.Modules.pullback U.hom).obj F) p))
      ((Sheaf.cohomologyAtObjectFunctor (τ.overTopology S) U p).obj
        ((SheafOfModules.toSheaf (Scheme.AssociatedModule.bigStructureSheaf τ S)).obj
          (Scheme.AssociatedModule.big τ S F))))

/- Remark 59.22.5 (3): The objectwise comparison holds on the small étale site. -/
@[stacks 03P3]
#check (AlgebraicGeometry.Scheme.AssociatedModule.cohomologyAtObject_isomorphic_small
    SmallStandardTopology.etale :
  ∀ (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]
    (U : SmallStandardTopology.site SmallStandardTopology.etale S) (p : ℕ)
    [HasSheafify (SmallStandardTopology.etale.topology S) AddCommGrpCat.{u}]
    [HasExt.{u}
      (Sheaf (SmallStandardTopology.etale.topology S) AddCommGrpCat.{u})],
    IsIsomorphic
      ((forget₂
          (ModuleCat Γ(((SmallStandardTopology.etale.toOver S).obj U).left, ⊤))
          AddCommGrpCat.{u}).obj
        (Scheme.Modules.cohomology
          ((Scheme.Modules.pullback ((SmallStandardTopology.etale.toOver S).obj U).hom).obj F)
            p))
      ((Sheaf.cohomologyAtObjectFunctor
          (SmallStandardTopology.etale.topology S) U p).obj
        ((SheafOfModules.toSheaf
            (Scheme.AssociatedModule.smallStructureSheaf SmallStandardTopology.etale S)).obj
          (Scheme.AssociatedModule.small SmallStandardTopology.etale S F))))
