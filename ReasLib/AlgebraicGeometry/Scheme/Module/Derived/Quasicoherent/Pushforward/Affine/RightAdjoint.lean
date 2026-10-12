/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- Under affine derived global-sections equivalences, the right adjoint of derived pushforward
along `Spec.map φ` is naturally isomorphic to derived coextension of scalars along `φ.hom`. -/
theorem affinePushforwardRightAdjoint_isomorphic
    {A B : CommRingCat.{u}} (φ : A ⟶ B) :
    IsIsomorphic
      ((affineGlobalSections A).inv ⋙
        (pushforwardCohomologyIn (Spec.map φ)).rightAdjoint ⋙ affineGlobalSections B)
      (ModuleCat.derivedCoextensionOfScalars φ.hom) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
