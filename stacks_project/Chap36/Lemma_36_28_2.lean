/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ProjectionFormula.ExtComparison

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalClosed
open RingedSite.Hom
open RingedSpace.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace ModuleDerived
namespace ProjectionFormula

/- Lemma 36.28.2: for every integer i and quasicoherent module F on S, the canonical
projection-formula comparison identifies degree-i cohomology of
Rf_*(Eᵛ ⊗ᴸ QG) ⊗ᴸ F with degree-i cohomology of
RHom(E, Q(G ⊗ f^*F)), naturally in F. -/
@[stacks 08ID] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula.extCohomologyComparison_isIso :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [IsNoetherian S] [LocallyOfFiniteType f]
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
      [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
      [KFlat.HomotopyTensorDescends S.toRingedSpace]
      [KFlat.TensorDescends S.toRingedSpace]
      [KFlat.IsLocalization S.toRingedSpace]
      [DerivedAdjunction.HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
      [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
      (i : ℤ),
      IsIso (extCohomologyComparison f E hE G i))

/- The comparison commutes with the connecting maps attached to every short exact
sequence of quasicoherent modules. -/
#check
  (AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula.extCohomologyComparison_boundary :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [IsNoetherian S] [LocallyOfFiniteType f]
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
      [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
      [KFlat.HomotopyTensorDescends S.toRingedSpace]
      [KFlat.TensorDescends S.toRingedSpace]
      [KFlat.IsLocalization S.toRingedSpace]
      [DerivedAdjunction.HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
      [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
      (T : ShortComplex S.Modules) (hT : T.ShortExact)
      (hT₁ : T.X₁.IsQuasicoherent) (hT₂ : T.X₂.IsQuasicoherent)
      (hT₃ : T.X₃.IsQuasicoherent) (i : ℤ),
      CommSq
        ((extCohomologyComparison f E hE G i).app ⟨T.X₃, hT₃⟩)
        (boundaryMap (source f (MonoidalClosed.dual E) G) hT i)
        (boundaryMap (extTarget f E hE G) hT i)
        ((extCohomologyComparison f E hE G (i + 1)).app ⟨T.X₁, hT₁⟩))

end ProjectionFormula
end ModuleDerived
end Scheme
end AlgebraicGeometry
