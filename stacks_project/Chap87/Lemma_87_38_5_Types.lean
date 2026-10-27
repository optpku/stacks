/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Types
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.LocalWeaklyAdic
public import ReasLib.AlgebraicGeometry.FormalSpectrum.AdicCompletion

/-!
# Local weak adicity

Typed compatibility checks for the canonical local weak-adicity API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]

#check (IsLocallyWeaklyAdic X : Prop)

#check (IsLocallyWeaklyAdic.iff X :
    IsLocallyWeaklyAdic X ↔
      ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
        (∀ i, AffineFormalAlgebraicSpace.IsWeaklyAdic (cover i)) ∧
          (∀ i, representableByAlgebraicSpaces (π i)) ∧
            (∀ i (ha : representableByAlgebraicSpaces (π i))
              {U : Over S} (ξ : yoneda.obj U ⟶ X),
              AlgebraicSpace.Etale
                (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
              Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π))

variable [IsLocallyWeaklyAdic X]

#check (IsLocallyWeaklyAdic.spec X :
    ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
      (∀ i, AffineFormalAlgebraicSpace.IsWeaklyAdic (cover i)) ∧
        (∀ i, representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π))

variable [AffineFormalAlgebraicSpace.IsWeaklyAdic X]

#check (IsLocallyWeaklyAdic.ofAffine X : IsLocallyWeaklyAdic X)

end AlgebraicGeometry.FormalAlgebraicSpace
