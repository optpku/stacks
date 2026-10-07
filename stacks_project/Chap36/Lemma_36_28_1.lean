module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ProjectionFormula.CohomologyComparison

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.DerivedCategory
open RingedSite.Hom RingedSpace.ModuleDerived

noncomputable section

universe u

/- Lemma 36.28.1: under the assumptions of Lemma 36.27.2, the canonical
boundary-compatible comparison from `RΓ(S, K ⊗ᴸ F[0])` to
`RΓ(X, E ⊗ᴸ Q(G• ⊗ f^*F))` induces an isomorphism on every degree of
cohomology for quasicoherent `F`. -/
@[stacks 0A1F] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula.cohomologyComparison_isIso :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [LocallyOfFiniteType f]
      (E : RingedSpace.ModuleDerived X.toRingedSpace)
      (hE : RingedSpace.ModuleDerived.IsPerfect E)
      (G : CochainComplex X.Modules ℤ)
      (hG_bounded : CochainComplex.bounded X.Modules G)
      [∀ n : ℤ, (G.X n).IsCoherent]
      [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom]
      [∀ n : ℤ, Scheme.Modules.HasProperSupportOver f
        (RingedSpace.ModuleDerived.cohomologySheaf (DerivedCategory.Q.obj G) n)]
      [KFlat.HomotopyTensorDescends X.toRingedSpace]
      [KFlat.TensorDescends X.toRingedSpace]
      [KFlat.IsLocalization X.toRingedSpace]
      [KFlat.HomotopyTensorDescends S.toRingedSpace]
      [KFlat.TensorDescends S.toRingedSpace]
      [KFlat.IsLocalization S.toRingedSpace]
      [DerivedAdjunction.HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
      [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
      (F : S.Modules) [F.IsQuasicoherent] (i : ℤ),
      IsIso
        (AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula.cohomologyMap
          (AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula.comparison f E G) F i))
