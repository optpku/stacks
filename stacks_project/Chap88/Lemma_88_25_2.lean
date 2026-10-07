module

public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap88.«88_27_0_1_Completion»

/-!
# Algebraization of morphisms of completions along a closed subset

A morphism of completions along `T` over a Noetherian affine algebraic space,
coming from a locally finite-type morphism étale off `T`, algebraizes after an
étale localization of the source that is an isomorphism on completions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace completionAlong

/-- The morphism of completions along `T` induced by a morphism of algebraic
spaces over `X`. -/
def mapOverHom {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S} (T : Closeds (Points X))
    (hY : Y ⟶ X) (hY' : Y' ⟶ X) (φ : Y' ⟶ Y) (hφ : φ ≫ hY = hY') :
    completionAlong Y' (T.preimage (Points.continuous_map hY')) ⟶
      completionAlong Y (T.preimage (Points.continuous_map hY)) :=
  mapOver T (Over.homMk φ hφ : Over.mk hY' ⟶ Over.mk hY)

/-- Lemma 88.25.2: Assume Noetherian affine algebraic spaces `X`, `X'`, and `Y`,
a closed subset `T ⊆ Points X`, a morphism `f : X' ⟶ X` locally of finite type
and étale over the open complement of `T`, a morphism `h : Y ⟶ X`, and a
morphism `α` of completions along `T` over `X`. Then there exist an affine
algebraic space `Y'`, an étale morphism `b : Y' ⟶ Y` inducing an isomorphism of
completions along `T`, and a morphism `a : Y' ⟶ X'` over `X` such that
`α = a_/T ∘ b_/T⁻¹`. -/
@[stacks 0AR3]
theorem exists_etaleFactor {S : Scheme.{u}} {X X' Y : AlgebraicSpace S}
    [IsAffine X] [IsAffine X'] [IsAffine Y]
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y]
    (T : Closeds (Points X)) (f : X' ⟶ X) [LocallyOfFiniteType f]
    (hf : Etale (openInverseImageTo f (openComplementι X T))) (h : Y ⟶ X)
    (α : completionAlong Y (T.preimage (Points.continuous_map h)) ⟶
      completionAlong X' (T.preimage (Points.continuous_map f)))
    (hα : α ≫ map f T = map h T) :
    ∃ (Y' : AlgebraicSpace S) (_ : IsAffine Y') (b : Y' ⟶ Y) (_ : Etale b)
      (a : Y' ⟶ X') (h_over : a ≫ f = b ≫ h)
      (_ : IsIso (mapOverHom T h (b ≫ h) b rfl)),
      α = inv (mapOverHom T h (b ≫ h) b rfl) ≫
        mapOverHom T f (b ≫ h) a h_over :=
  sorry

/-- Completing `b` and `a` over `X` recovers `α` without inverses, as
`b_/T ≫ α = a_/T`. -/
theorem mapOver_comp_eq {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    (T : Closeds (Points X)) (f : X' ⟶ X) (h : Y ⟶ X)
    (α : completionAlong Y (T.preimage (Points.continuous_map h)) ⟶
      completionAlong X' (T.preimage (Points.continuous_map f)))
    (b : Y' ⟶ Y) (a : Y' ⟶ X') (h_over : a ≫ f = b ≫ h)
    [IsIso (mapOverHom T h (b ≫ h) b rfl)]
    (hα : α = inv (mapOverHom T h (b ≫ h) b rfl) ≫
      mapOverHom T f (b ≫ h) a h_over) :
    mapOverHom T h (b ≫ h) b rfl ≫ α =
      mapOverHom T f (b ≫ h) a h_over :=
  sorry

end completionAlong

end AlgebraicGeometry.AlgebraicSpace

