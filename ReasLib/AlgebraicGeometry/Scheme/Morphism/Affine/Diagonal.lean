module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.Tactic.CrossRefAttribute

/-!
# Affine morphisms and affine diagonals

An affine composite may be cancelled on the right when the second morphism has affine diagonal.
This gives the corresponding criteria for separated morphisms and for morphisms from affine
schemes.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- If a composite is affine and the second map has affine diagonal, then the first map is affine. -/
@[stacks 01SG]
theorem isAffineHom_of_isAffineHom_comp_of_affineDiagonal
    {X Y S : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ S)
    [IsAffineHom (g ≫ f)] [IsAffineHom (pullback.diagonal f)] : IsAffineHom g := by
  let P : MorphismProperty Scheme := @IsAffineHom
  -- Local instance justification (proof-local temporary data): instantiate affine right-cancellation with the affine-diagonal property.
  letI : P.HasOfPostcompProperty P.diagonal :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr le_rfl
  exact MorphismProperty.of_postcomp (W' := P.diagonal) P g f
    (show IsAffineHom (pullback.diagonal f) from inferInstance)
    (show IsAffineHom (g ≫ f) from inferInstance)

/-- A morphism from an affine scheme to a scheme with affine absolute diagonal is affine. -/
@[stacks 01SG]
theorem isAffineHom_of_isAffine_of_affineDiagonal
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsAffine X]
    [IsAffineHom (prod.lift (𝟙 Y) (𝟙 Y))] : IsAffineHom g := by
  -- Local instance justification (proof-local temporary data): transport the affine absolute diagonal across the product-pullback isomorphism.
  letI : IsAffineHom (pullback.diagonal (terminal.from Y)) := by
    have heq :
        prod.lift (𝟙 Y) (𝟙 Y) ≫ (prodIsoPullback Y Y).hom =
          pullback.diagonal (terminal.from Y) := by
      apply pullback.hom_ext
      · simp only [Category.assoc, prodIsoPullback_hom_fst, prod.lift_fst,
          pullback.diagonal_fst]
      · simp only [Category.assoc, prodIsoPullback_hom_snd, prod.lift_snd,
          pullback.diagonal_snd]
    rw [← heq]
    exact (MorphismProperty.cancel_right_of_respectsIso (@IsAffineHom)
      (prod.lift (𝟙 Y) (𝟙 Y)) (prodIsoPullback Y Y).hom).mpr inferInstance
  exact isAffineHom_of_isAffineHom_comp_of_affineDiagonal g (terminal.from Y)

/-- A morphism from an affine scheme to a separated scheme is affine. -/
@[stacks 01SG]
theorem isAffineHom_of_isAffine_of_isSeparated
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsAffine X] [Y.IsSeparated] : IsAffineHom g := by
  exact isAffineHom_of_isAffine_of_affineDiagonal g

namespace Scheme

/-- The absolute diagonal of a scheme is affine exactly when intersections of affine opens are
affine. -/
theorem affineDiagonal_iff_affineOpenIntersections
    (X : Scheme.{u}) :
    IsAffineHom (prod.lift (𝟙 X) (𝟙 X)) ↔
      ∀ U V : X.affineOpens, IsAffineOpen (U.1 ⊓ V.1) := sorry

/-- If every pairwise intersection of affine opens is affine, there is an open cover whose every
nonempty finite intersection is affine. -/
theorem exists_affineIntersectionOpenCover_of_affineOpenIntersections
    (X : Scheme.{u})
    (hX : ∀ U V : X.affineOpens, IsAffineOpen (U.1 ⊓ V.1)) :
    ∃ (I : Type u) (U : I → X.Opens), TopologicalSpace.IsOpenCover U ∧
      ∀ p : ℕ, ∀ σ : Fin (p + 1) → I, IsAffineOpen (⨅ a, U (σ a)) := sorry

/-- An open cover whose every nonempty finite intersection is affine gives an affine absolute
diagonal. -/
theorem affineDiagonal_of_exists_affineIntersectionOpenCover
    (X : Scheme.{u})
    (hX :
      ∃ (I : Type u) (U : I → X.Opens), TopologicalSpace.IsOpenCover U ∧
        ∀ p : ℕ, ∀ σ : Fin (p + 1) → I, IsAffineOpen (⨅ a, U (σ a))) :
    IsAffineHom (prod.lift (𝟙 X) (𝟙 X)) := sorry

/-- The absolute diagonal of a separated scheme is affine. -/
theorem affineDiagonal_of_isSeparated
    (X : Scheme.{u}) [X.IsSeparated] :
    IsAffineHom (prod.lift (𝟙 X) (𝟙 X)) := sorry

/-- A scheme with affine absolute diagonal is quasi-separated. -/
instance quasiSeparatedSpace_of_affineDiagonal
    (X : Scheme.{u}) [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))] :
    QuasiSeparatedSpace X := sorry

end Scheme

end AlgebraicGeometry
