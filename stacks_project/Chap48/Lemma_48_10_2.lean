/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.BaseChange.InternalHom.PseudoCoherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSite.Hom RingedSpace.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.TorIndependentBaseChange

/- Lemma 48.10.2: in a Tor-independent cartesian square with `i : Z ⟶ X` a
pseudo-coherent closed immersion and `f : X' ⟶ X` flat, the right-adjoint base-change
map (48.10.0.1) is an isomorphism for every `K ∈ D⁺_QCoh(𝒪_X)`. -/
@[stacks 0E2M] #check
  (AlgebraicGeometry.Scheme.TorIndependentBaseChange.rightAdjoint_baseChange_isIso_of_flat_of_pseudoCoherent :
    {Z' Z X' X : Scheme.{u}} →
    (g : Z' ⟶ Z) → (i' : Z' ⟶ X') → (i : Z ⟶ X) → (f : X' ⟶ X) →
    [DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom i.toShHom)]
    → [DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom i'.toShHom)]
    → [IsIso (RingedSpace.modulePullbackDerived.compComparison
      i'.toShHom f.toShHom)]
    → [IsIso (RingedSpace.modulePullbackDerived.compComparison
      g.toShHom i.toShHom)]
    → [KFlat.HomotopyTensorDescends X.toRingedSpace]
    → [KFlat.TensorDescends X.toRingedSpace]
    → [KFlat.IsLocalization X.toRingedSpace]
    → [KFlat.HomotopyTensorDescends X'.toRingedSpace]
    → [KFlat.TensorDescends X'.toRingedSpace]
    → [KFlat.IsLocalization X'.toRingedSpace]
    → [(RingedSpace.modulePullbackDerived f.toShHom).Monoidal]
    → (sq : IsPullback g i' i f) → [IsClosedImmersion i]
    → (hTor : Scheme.TorIndependentOver (Over.mk i) (Over.mk f))
    → [Flat f] → [PseudoCoherent i]
    → (rHomOZ : RingedSpace.ModuleDerived X.toRingedSpace ⥤
      RingedSpace.ModuleDerived Z.toRingedSpace)
    → (rHomOZPrime : RingedSpace.ModuleDerived X'.toRingedSpace ⥤
      RingedSpace.ModuleDerived Z'.toRingedSpace)
    → (iAdj : RingedSpace.moduleDerivedPushforward i.toShHom ⊣ rHomOZ)
    → (iPrimeAdj : RingedSpace.moduleDerivedPushforward i'.toShHom ⊣ rHomOZPrime)
    → (baseChangeIso :
      RingedSpace.modulePullbackDerived g.toShHom ⋙
          RingedSpace.moduleDerivedPushforward i'.toShHom ≅
        RingedSpace.moduleDerivedPushforward i.toShHom ⋙
          RingedSpace.modulePullbackDerived f.toShHom)
    → (h_baseChange : baseChangeIso.inv =
      Hom.DerivedBaseChange.map sq.toCommSq)
    → (K : Scheme.DerivedQCoh.Plus X) →
    IsIso (CategoryTheory.DerivedBaseChange.app
      iAdj iPrimeAdj baseChangeIso K.obj.obj))

end AlgebraicGeometry.Scheme.TorIndependentBaseChange
