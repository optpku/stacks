/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Composition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ProjectionFormula
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Chow.Derived

/-!
# Restriction of derived Chow presentations

This file records the morphism between the chosen opens of a derived Chow presentation and the
corresponding restricted derived-pushforward identity.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.ModuleDerived
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.DerivedChowPresentation

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of A)} {x : X}

/-- The morphism from the chosen source open to the chosen projective open induced by the two
projections of a derived Chow presentation. -/
noncomputable def openMorphism (M : DerivedChowPresentation f x) :
    M.U.toScheme ⟶ M.V.toScheme :=
  (@asIso _ _ _ _ (M.sourceProjection ∣_ M.U) M.isIsoOverSourceOpen).inv ≫
    (M.I.subscheme.isoOfEq M.preimageSourceOpen_eq_preimageProjectiveOpen).hom ≫
      (M.projectiveProjection ∣_ M.V)

/-- The morphism between the chosen opens of a derived Chow presentation is a closed
immersion. -/
theorem openMorphism_isClosedImmersion (M : DerivedChowPresentation f x) :
    IsClosedImmersion M.openMorphism := sorry

/-- The morphism between the chosen opens of a derived Chow presentation is of finite
presentation. -/
theorem openMorphism_finitePresentation [Scheme.Hom.FinitePresentation f]
    (M : DerivedChowPresentation f x) :
    Scheme.Hom.FinitePresentation M.openMorphism := sorry

/-- For a derived Chow presentation, restricting the derived pushforward of the tensor product
of a pulled-back quasicoherent complex with the presentation complex to the chosen projective
open is isomorphic to the derived pushforward of its restriction to the chosen source open. -/
theorem pushforwardTensor_restriction_isomorphic
    (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f]
    [Scheme.Hom.FinitePresentation f] (x : X) (M : DerivedChowPresentation f x)
    [h_homotopyTensor : KFlat.HomotopyTensorDescends
      (pullback f M.P.hom).toRingedSpace]
    [h_tensor : KFlat.TensorDescends (pullback f M.P.hom).toRingedSpace]
    [h_localization : KFlat.IsLocalization (pullback f M.P.hom).toRingedSpace]
    (K : Scheme.DerivedQCoh X) :
    IsIsomorphic
      ((RingedSpace.moduleRestrictionToOpenDerived M.P.scheme.toRingedSpace M.V).obj
        ((RingedSpace.moduleDerivedPushforward (pullback.snd f M.P.hom).toShHom).obj
          ((RingedSpace.modulePullbackDerived (pullback.fst f M.P.hom).toShHom).obj K.obj ⊗
            M.E)))
      ((RingedSpace.moduleDerivedPushforward M.openMorphism.toShHom).obj
        ((RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace M.U).obj K.obj)) := sorry

end AlgebraicGeometry.DerivedChowPresentation
