module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.Affine.RightAdjoint

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Example 48.3.2 (1): for a ring map `φ : A ⟶ B`, derived pushforward along
`Spec.map φ : Spec B ⟶ Spec A` corresponds to derived restriction of scalars under the
affine equivalences `D(B) ≃ D_QCoh(𝒪_(Spec B))` and `D(A) ≃ D_QCoh(𝒪_(Spec A))`. -/
@[stacks 0A9F] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.affinePushforwardSquare_isomorphic :
    ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B),
      IsIsomorphic
        ((affineGlobalSections B).inv ⋙ pushforwardCohomologyIn (Spec.map φ))
        (ModuleCat.derivedRestrictionOfScalars φ.hom ⋙
          (affineGlobalSections A).inv))

/- Example 48.3.2 (2): the right adjoint of affine derived pushforward corresponds,
under affine derived global sections, to `RHom_A(B, -)`, represented by derived
coextension of scalars. -/
@[stacks 0A9F] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.affinePushforwardRightAdjoint_isomorphic :
    ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B),
      IsIsomorphic
        ((affineGlobalSections A).inv ⋙
          (pushforwardCohomologyIn (Spec.map φ)).rightAdjoint ⋙ affineGlobalSections B)
        (ModuleCat.derivedCoextensionOfScalars φ.hom))

end AlgebraicGeometry.Scheme.DerivedQCoh
