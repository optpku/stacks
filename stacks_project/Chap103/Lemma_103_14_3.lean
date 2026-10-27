/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Cohomology.Restriction
import StacksCheckRecall

/-!
# Lemma 103.14.3

Restriction preserves global and slice cohomology of abelian sheaves and
modules. The explicit existence hypotheses stand for the Stacks bounded-site
size convention.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.GroupoidsOver CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/- Lemma 103.14.3: For an algebraic stack `X` and an abelian sheaf `F` on
`X.etaleTopology`, `H^p(X_étale, F)` agrees with
`H^p(X_lisse,étale, g⁻¹ F)`, where `g⁻¹` is restriction along
`lisseEtaleInclusion`. -/
@[stacks 0GR0] #check (AlgebraicGeometry.AlgebraicStack.cohomology_lisseEtale :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
    [HasSheafify (lisseEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.etaleTopology AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u})]
    (F : Sheaf X.etaleTopology AddCommGrpCat.{u}) (p : ℕ),
    IsIsomorphic ((Sheaf.functorH X.etaleTopology p).obj F)
      ((Sheaf.functorH (lisseEtaleTopology X) p).obj
        (((lisseEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u}
            (lisseEtaleTopology X) X.etaleTopology).obj F)))

/- Lemma 103.14.3: For an algebraic stack `X`, an abelian sheaf `F` on
`X.etaleTopology`, and an object `x` of `lisseEtaleSite X`, `H^p(x, F)`
agrees with `H^p(X_lisse,étale / x, g⁻¹ F)`. -/
@[stacks 0GR0] #check (AlgebraicGeometry.AlgebraicStack.cohomology_lisseEtale_over :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
    [HasSheafify (lisseEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.etaleTopology AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u})]
    (x : lisseEtaleSite X)
    [HasSheafify ((lisseEtaleTopology X).over x) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf ((lisseEtaleTopology X).over x) AddCommGrpCat.{u})]
    (F : Sheaf X.etaleTopology AddCommGrpCat.{u}) (p : ℕ),
    IsIsomorphic (F.H' p ((lisseEtaleInclusion X).obj x))
      ((Sheaf.functorH ((lisseEtaleTopology X).over x) p).obj
        ((((lisseEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u}
              (lisseEtaleTopology X) X.etaleTopology).obj F).over x)))

/- Lemma 103.14.3: For an algebraic stack `X` and an abelian sheaf `F` on
`inheritedFppfTopology X`, `H^p(X_fppf, F)` agrees with
`H^p(X_flat,fppf, g⁻¹ F)`, where `g⁻¹` is restriction along
`flatFppfInclusion`. -/
@[stacks 0GR0] #check (AlgebraicGeometry.AlgebraicStack.cohomology_flatFppf :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (inheritedFppfTopology X) AddCommGrpCat.{u}]
    [HasSheafify (flatFppfTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf (flatFppfTopology X) AddCommGrpCat.{u})]
    (F : Sheaf (inheritedFppfTopology X) AddCommGrpCat.{u}) (p : ℕ),
    IsIsomorphic ((Sheaf.functorH (inheritedFppfTopology X) p).obj F)
      ((Sheaf.functorH (flatFppfTopology X) p).obj
        (((flatFppfInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u}
            (flatFppfTopology X) (inheritedFppfTopology X)).obj F)))

/- Lemma 103.14.3: For an algebraic stack `X`, an abelian sheaf `F` on
`inheritedFppfTopology X`, and an object `x` of `flatFppfSite X`, `H^p(x, F)`
agrees with `H^p(X_flat,fppf / x, g⁻¹ F)`. -/
@[stacks 0GR0] #check (AlgebraicGeometry.AlgebraicStack.cohomology_flatFppf_over :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (inheritedFppfTopology X) AddCommGrpCat.{u}]
    [HasSheafify (flatFppfTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf (flatFppfTopology X) AddCommGrpCat.{u})]
    (x : flatFppfSite X)
    [HasSheafify ((flatFppfTopology X).over x) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf ((flatFppfTopology X).over x) AddCommGrpCat.{u})]
    (F : Sheaf (inheritedFppfTopology X) AddCommGrpCat.{u}) (p : ℕ),
    IsIsomorphic (F.H' p ((flatFppfInclusion X).obj x))
      ((Sheaf.functorH ((flatFppfTopology X).over x) p).obj
        ((((flatFppfInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u}
              (flatFppfTopology X) (inheritedFppfTopology X)).obj F).over x)))

/- Lemma 103.14.3: Restriction of étale `𝒪_X`-modules along the lisse-étale ringed morphism
does not change global cohomology. -/
@[stacks 0GR0] #check (AlgebraicGeometry.AlgebraicStack.cohomology_lisseEtale_modules :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
    [HasSheafify (lisseEtaleTopology X) AddCommGrpCat.{u}]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)]
    [HasExt.{u} (Sheaf X.etaleTopology AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u})]
    (F : SheafOfModules.{u} (etaleStructureSheaf X)) (p : ℕ),
    IsIsomorphic
      ((Sheaf.functorH X.etaleTopology p).obj
        ((SheafOfModules.toSheaf (etaleStructureSheaf X)).obj F))
      ((Sheaf.functorH (lisseEtaleTopology X) p).obj
        ((SheafOfModules.toSheaf (lisseEtaleStructureSheaf X)).obj
          ((lisseEtaleModulePullback X).obj F))))

/- Lemma 103.14.3: Restriction of étale `𝒪_X`-modules along the lisse-étale ringed morphism
does not change cohomology on `X_lisse,étale / x`. -/
@[stacks 0GR0] #check (AlgebraicGeometry.AlgebraicStack.cohomology_lisseEtale_over_modules :
  ∀ (X : GroupoidsOver S)
    [AlgebraicStack X]
    [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
    [HasSheafify (lisseEtaleTopology X) AddCommGrpCat.{u}]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)]
    [HasExt.{u} (Sheaf X.etaleTopology AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u})]
    (x : lisseEtaleSite X)
    [HasSheafify ((lisseEtaleTopology X).over x) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf ((lisseEtaleTopology X).over x) AddCommGrpCat.{u})]
    (F : SheafOfModules.{u} (etaleStructureSheaf X)) (p : ℕ),
    IsIsomorphic
      (((SheafOfModules.toSheaf (etaleStructureSheaf X)).obj F).H' p
        ((lisseEtaleInclusion X).obj x))
      ((Sheaf.functorH ((lisseEtaleTopology X).over x) p).obj
        (((SheafOfModules.toSheaf (lisseEtaleStructureSheaf X)).obj
            ((lisseEtaleModulePullback X).obj F)).over x)))

/- Lemma 103.14.3: Restriction of fppf `𝒪_X`-modules along the flat-fppf ringed morphism
does not change global cohomology. -/
@[stacks 0GR0] #check (AlgebraicGeometry.AlgebraicStack.cohomology_flatFppf_modules :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (inheritedFppfTopology X) AddCommGrpCat.{u}]
    [HasSheafify (flatFppfTopology X) AddCommGrpCat.{u}]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [HasExt.{u} (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf (flatFppfTopology X) AddCommGrpCat.{u})]
    (F : SheafOfModules.{u} (structureSheaf X)) (p : ℕ),
    IsIsomorphic
      ((Sheaf.functorH (inheritedFppfTopology X) p).obj
        ((SheafOfModules.toSheaf (structureSheaf X)).obj F))
      ((Sheaf.functorH (flatFppfTopology X) p).obj
        ((SheafOfModules.toSheaf (flatFppfStructureSheaf X)).obj
          ((flatFppfModulePullback X).obj F))))

/- Lemma 103.14.3: Restriction of fppf `𝒪_X`-modules along the flat-fppf ringed morphism
does not change cohomology on `X_flat,fppf / x`. -/
@[stacks 0GR0] #check (AlgebraicGeometry.AlgebraicStack.cohomology_flatFppf_over_modules :
  ∀ (X : GroupoidsOver S)
    [AlgebraicStack X]
    [HasSheafify (inheritedFppfTopology X) AddCommGrpCat.{u}]
    [HasSheafify (flatFppfTopology X) AddCommGrpCat.{u}]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [HasExt.{u} (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf (flatFppfTopology X) AddCommGrpCat.{u})]
    (x : flatFppfSite X)
    [HasSheafify ((flatFppfTopology X).over x) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf ((flatFppfTopology X).over x) AddCommGrpCat.{u})]
    (F : SheafOfModules.{u} (structureSheaf X)) (p : ℕ),
    IsIsomorphic
      (((SheafOfModules.toSheaf (structureSheaf X)).obj F).H' p
        ((flatFppfInclusion X).obj x))
      ((Sheaf.functorH ((flatFppfTopology X).over x) p).obj
        (((SheafOfModules.toSheaf (flatFppfStructureSheaf X)).obj
            ((flatFppfModulePullback X).obj F)).over x)))

end AlgebraicGeometry.AlgebraicStack
