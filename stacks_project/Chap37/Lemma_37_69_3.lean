/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Chow.Derived.Restriction
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.ModuleDerived
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry

/- Lemma 37.69.3: for a derived Chow presentation, restricting
`Rq_*(Lp^*K ⊗ᴸ E)` to `V` is isomorphic to the derived pushforward of `K|_U` along the
finitely presented closed immersion `c ∘ (b|_U)⁻¹ : U ⟶ V`. -/
@[stacks 0CSK] #check
  (AlgebraicGeometry.DerivedChowPresentation.pushforwardTensor_restriction_isomorphic :
    ∀ {A : Type u} [CommRing A] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f]
      [Scheme.Hom.FinitePresentation f] (x : X) (M : DerivedChowPresentation f x)
      [KFlat.HomotopyTensorDescends (pullback f M.P.hom).toRingedSpace]
      [KFlat.TensorDescends (pullback f M.P.hom).toRingedSpace]
      [KFlat.IsLocalization (pullback f M.P.hom).toRingedSpace]
      (K : Scheme.DerivedQCoh X),
      IsIsomorphic
        ((RingedSpace.moduleRestrictionToOpenDerived M.P.scheme.toRingedSpace M.V).obj
          ((RingedSpace.moduleDerivedPushforward (pullback.snd f M.P.hom).toShHom).obj
            ((RingedSpace.modulePullbackDerived (pullback.fst f M.P.hom).toShHom).obj K.obj ⊗
              M.E)))
        ((RingedSpace.moduleDerivedPushforward M.openMorphism.toShHom).obj
          ((RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace M.U).obj K.obj)))

#check
  (AlgebraicGeometry.DerivedChowPresentation.openMorphism_isClosedImmersion :
    ∀ {A : Type u} [CommRing A] {X : Scheme.{u}}
      {f : X ⟶ Spec (CommRingCat.of A)} {x : X} (M : DerivedChowPresentation f x),
      IsClosedImmersion M.openMorphism)

#check
  (AlgebraicGeometry.DerivedChowPresentation.openMorphism_finitePresentation :
    ∀ {A : Type u} [CommRing A] {X : Scheme.{u}}
      {f : X ⟶ Spec (CommRingCat.of A)} {x : X} [Scheme.Hom.FinitePresentation f]
      (M : DerivedChowPresentation f x),
      Scheme.Hom.FinitePresentation M.openMorphism)

end AlgebraicGeometry
