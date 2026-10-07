module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Small
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.Small
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Singleton.Over
public import ReasLib.CategoryTheory.Limits.Over.Products
public import ReasLib.CategoryTheory.Sites.Cech.Refinement

/-!
# Čech comparison for coproduct singleton families

This module records the canonical Čech-complex comparison isomorphisms induced by replacing a
finite family with the singleton family on the coproduct of its objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Limits.FormalCoproduct.Over

noncomputable section

universe u

namespace AlgebraicGeometry.StandardTopology

/-- For a standard big site over a scheme, the Čech-complex map from a finite family's
coproduct-singleton replacement to the original family is an isomorphism for abelian sheaves. -/
theorem coproductSingletonCechMap_isIso
    (τ : StandardTopology) (S : Scheme.{u}) (U : Over S)
    (K : FormalCoproduct.{u} (Over U)) [Finite K.I]
    [HasCoproduct (fun i ↦ (K.obj i).left)]
    (F : Sheaf (τ.overTopology S) AddCommGrpCat.{u}) :
    IsIso (cechComplexMapOfRefinement U
      (coproductSingleton K).obj K.obj (toCoproductSingleton K) F.obj) := sorry

end AlgebraicGeometry.StandardTopology

namespace AlgebraicGeometry.Scheme.Etale

/-- On the small étale site of a scheme, the Čech-complex map from a finite family's
coproduct-singleton replacement to the original family is an isomorphism for abelian sheaves. -/
theorem coproductSingletonCechMap_isIso
    (S : Scheme.{u}) (U : S.Etale)
    (K : FormalCoproduct.{u} (Over U)) [Finite K.I]
    [HasCoproduct (fun i ↦ (K.obj i).left)]
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso (cechComplexMapOfRefinement U
      (coproductSingleton K).obj K.obj (toCoproductSingleton K) F.obj) := sorry

end AlgebraicGeometry.Scheme.Etale

namespace AlgebraicGeometry.Scheme.Zariski

/-- On the small Zariski site of a scheme, the Čech-complex map from a finite family's
coproduct-singleton replacement to the original family is an isomorphism for abelian sheaves. -/
theorem coproductSingletonCechMap_isIso
    (S : Scheme.{u}) (U : S.smallZariskiSite)
    (K : FormalCoproduct.{u} (Over U)) [Finite K.I]
    [HasCoproduct (fun i ↦ (K.obj i).left)]
    (F : Sheaf S.smallZariskiTopology AddCommGrpCat.{u}) :
    IsIso (cechComplexMapOfRefinement U
      (coproductSingleton K).obj K.obj (toCoproductSingleton K) F.obj) := sorry

end AlgebraicGeometry.Scheme.Zariski
