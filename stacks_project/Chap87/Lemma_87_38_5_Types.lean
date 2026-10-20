/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Types
public import stacks_project.Chap87.Lemma_87_38_4_Completion

/-!
# Types of the formal completion

Formal-space atlas data and compatible adic/Noetherian presentations use their canonical
public owners. The source-specific weakly adic property uses its presheaf formal-spectrum API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- A formal algebraic space over `S` is locally weakly adic when it admits an
étale atlas by weakly adic affine formal algebraic spaces. -/
@[mk_iff]
class IsLocallyWeaklyAdic {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] : Prop where
  /-- There is an étale atlas by weakly adic affine formal algebraic spaces,
  representable by algebraic spaces and jointly fppf-locally surjective. -/
  exists_atlas :
    ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
      (∀ i, AffineFormalAlgebraicSpace.IsWeaklyAdic (cover i)) ∧
        (∀ i, representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π)

namespace IsLocallyWeaklyAdic

/-- A locally weakly adic formal algebraic space admits an étale atlas by
weakly adic affine formal algebraic spaces. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyWeaklyAdic X] :
    ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
      (∀ i, AffineFormalAlgebraicSpace.IsWeaklyAdic (cover i)) ∧
        (∀ i, representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) :=
  sorry

/-- Locally weakly adic formal algebraic spaces are exactly formal algebraic
spaces with an étale atlas by weakly adic affine charts. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] :
    IsLocallyWeaklyAdic X ↔
      ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
        (∀ i, AffineFormalAlgebraicSpace.IsWeaklyAdic (cover i)) ∧
          (∀ i, representableByAlgebraicSpaces (π i)) ∧
            (∀ i (ha : representableByAlgebraicSpaces (π i))
              {U : Over S} (ξ : yoneda.obj U ⟶ X),
              AlgebraicSpace.Etale
                (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
              Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) :=
  sorry

/-- A weakly adic affine formal algebraic space that is a formal algebraic space
is locally weakly adic. -/
instance ofAffine {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [AffineFormalAlgebraicSpace.IsWeaklyAdic X] :
    IsLocallyWeaklyAdic X :=
  sorry

end IsLocallyWeaklyAdic

end AlgebraicGeometry.FormalAlgebraicSpace
