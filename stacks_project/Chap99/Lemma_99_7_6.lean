/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap99.Lemma_99_7_6_Equalizer

/-!
# Lemma 99.7.6

In Situation 99.7.1, an fpqc covering `{X_i ⟶ X}` together with fpqc coverings
`{X_ijk ⟶ X_i ×_X X_j}` presents `Q_{F/X/B}(T)` as the equalizer of the Čech
parallel pair `∏_i Q_{F_i/X_i/B}(T) ⇉ ∏_{i,j,k} Q_{F_ijk/X_ijk/B}(T)` for every
scheme `T` over `B`. The same holds for `Q^{fp}_{F/X/B}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace.Quot

noncomputable section

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace.Quot

/-- Lemma 99.7.6 (1): in Situation 99.7.1, an fpqc covering `{X_i ⟶ X}` together
with fpqc coverings `{X_ijk ⟶ X_i ×_X X_j}` presents `Q_{F/X/B}(T)` as the
equalizer of the two restrictions
`∏_i Q_{F_i/X_i/B}(T) ⇉ ∏_{i,j,k} Q_{F_ijk/X_ijk/B}(T)`
for every scheme `T` over `B`. -/
@[stacks 08IV]
theorem functor_covering_equalizer {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    {family : I → Over X} (hfamily : FpqcCovering family) {K : I → I → Type w}
    {overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom)}
    (hoverlap : ∀ i j, FpqcCovering (overlap i j)) (σ : SchemesOver B)
    (s : (i : I) → (memberFunctor f F family i).obj (op σ))
    (hs : coveringPrFst f F family overlap σ s =
      coveringPrSnd f F family overlap σ s) :
    ∃! u, coveringHom f F family σ u = s :=
  sorry

/-- The restriction map `Q_{F/X/B}(T) ⟶ ∏_i Q_{F_i/X_i/B}(T)` is injective. -/
theorem coveringHom_injective {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    {family : I → Over X} (hfamily : FpqcCovering family) {K : I → I → Type w}
    {overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom)}
    (hoverlap : ∀ i j, FpqcCovering (overlap i j)) (σ : SchemesOver B) :
    Function.Injective (coveringHom f F family σ) :=
  sorry

/-- A family in `∏_i Q_{F_i/X_i/B}(T)` comes from `Q_{F/X/B}(T)` if and only if
it is equalized by `pr₀^*` and `pr₁^*`. -/
theorem coveringHom_eq_iff {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    {family : I → Over X} (hfamily : FpqcCovering family) {K : I → I → Type w}
    {overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom)}
    (hoverlap : ∀ i j, FpqcCovering (overlap i j)) (σ : SchemesOver B)
    (s : (i : I) → (memberFunctor f F family i).obj (op σ)) :
    (∃ u, coveringHom f F family σ u = s) ↔
      coveringPrFst f F family overlap σ s =
        coveringPrSnd f F family overlap σ s :=
  sorry

/-- Lemma 99.7.6 (2): in Situation 99.7.1, an fpqc covering `{X_i ⟶ X}` together
with fpqc coverings `{X_ijk ⟶ X_i ×_X X_j}` presents `Q^{fp}_{F/X/B}(T)` as the
equalizer of the two restrictions
`∏_i Q^{fp}_{F_i/X_i/B}(T) ⇉ ∏_{i,j,k} Q^{fp}_{F_ijk/X_ijk/B}(T)`
for every scheme `T` over `B`. -/
@[stacks 08IV]
theorem fpFunctor_covering_equalizer {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    {family : I → Over X} (hfamily : FpqcCovering family) {K : I → I → Type w}
    {overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom)}
    (hoverlap : ∀ i j, FpqcCovering (overlap i j)) (σ : SchemesOver B)
    (s : (i : I) → (fpMemberFunctor f F family i).obj (op σ))
    (hs : fpCoveringPrFst f F family overlap σ s =
      fpCoveringPrSnd f F family overlap σ s) :
    ∃! u, fpCoveringHom f F family σ u = s :=
  sorry

/-- The restriction map `Q^{fp}_{F/X/B}(T) ⟶ ∏_i Q^{fp}_{F_i/X_i/B}(T)` is
injective. -/
theorem fpCoveringHom_injective {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    {family : I → Over X} (hfamily : FpqcCovering family) {K : I → I → Type w}
    {overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom)}
    (hoverlap : ∀ i j, FpqcCovering (overlap i j)) (σ : SchemesOver B) :
    Function.Injective (fpCoveringHom f F family σ) :=
  sorry

/-- A family in `∏_i Q^{fp}_{F_i/X_i/B}(T)` comes from `Q^{fp}_{F/X/B}(T)` if and
only if it is equalized by `pr₀^*` and `pr₁^*`. -/
theorem fpCoveringHom_eq_iff {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    {family : I → Over X} (hfamily : FpqcCovering family) {K : I → I → Type w}
    {overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom)}
    (hoverlap : ∀ i j, FpqcCovering (overlap i j)) (σ : SchemesOver B)
    (s : (i : I) → (fpMemberFunctor f F family i).obj (op σ)) :
    (∃ u, fpCoveringHom f F family σ u = s) ↔
      fpCoveringPrFst f F family overlap σ s =
        fpCoveringPrSnd f F family overlap σ s :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
