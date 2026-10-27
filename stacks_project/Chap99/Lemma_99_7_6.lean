/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Descent
import StacksCheckRecall

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

/- Lemma 99.7.6 (1): fpqc descent for quotient points. -/
@[stacks 08IV] #check (AlgebraicGeometry.AlgebraicSpace.Quot.functor_covering_equalizer :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    {family : I → Over X} (hfamily : FpqcCovering family) {K : I → I → Type w}
    {overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom)}
    (hoverlap : ∀ i j, FpqcCovering (overlap i j)) (σ : SchemeOver B)
    (s : (i : I) → (memberFunctor f F family i).obj (op σ))
    (hs : coveringPrFst f F family hfamily.flat overlap (fun i j ↦ (hoverlap i j).flat) σ s =
      coveringPrSnd f F family hfamily.flat overlap (fun i j ↦ (hoverlap i j).flat) σ s),
    ∃! u, coveringHom f F family hfamily.flat σ u = s)

#check (AlgebraicGeometry.AlgebraicSpace.Quot.coveringHom_injective :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    {family : I → Over X} (hfamily : FpqcCovering family) {K : I → I → Type w}
    {overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom)}
    (hoverlap : ∀ i j, FpqcCovering (overlap i j)) (σ : SchemeOver B),
    Function.Injective (coveringHom f F family hfamily.flat σ))

#check (AlgebraicGeometry.AlgebraicSpace.Quot.coveringHom_eq_iff :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    {family : I → Over X} (hfamily : FpqcCovering family) {K : I → I → Type w}
    {overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom)}
    (hoverlap : ∀ i j, FpqcCovering (overlap i j)) (σ : SchemeOver B)
    (s : (i : I) → (memberFunctor f F family i).obj (op σ)),
    (∃ u, coveringHom f F family hfamily.flat σ u = s) ↔
      coveringPrFst f F family hfamily.flat overlap (fun i j ↦ (hoverlap i j).flat) σ s =
        coveringPrSnd f F family hfamily.flat overlap (fun i j ↦ (hoverlap i j).flat) σ s)

/- Lemma 99.7.6 (2): fpqc descent for finitely presented quotient points. -/
@[stacks 08IV] #check (AlgebraicGeometry.AlgebraicSpace.Quot.fpFunctor_covering_equalizer :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    {family : I → Over X} (hfamily : FpqcCovering family) {K : I → I → Type w}
    {overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom)}
    (hoverlap : ∀ i j, FpqcCovering (overlap i j)) (σ : SchemeOver B)
    (s : (i : I) → (fpMemberFunctor f F family i).obj (op σ))
    (hs : fpCoveringPrFst f F family hfamily.flat overlap (fun i j ↦ (hoverlap i j).flat) σ s =
      fpCoveringPrSnd f F family hfamily.flat overlap (fun i j ↦ (hoverlap i j).flat) σ s),
    ∃! u, fpCoveringHom f F family hfamily.flat σ u = s)

#check (AlgebraicGeometry.AlgebraicSpace.Quot.fpCoveringHom_injective :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    {family : I → Over X} (hfamily : FpqcCovering family) {K : I → I → Type w}
    {overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom)}
    (hoverlap : ∀ i j, FpqcCovering (overlap i j)) (σ : SchemeOver B),
    Function.Injective (fpCoveringHom f F family hfamily.flat σ))

#check (AlgebraicGeometry.AlgebraicSpace.Quot.fpCoveringHom_eq_iff :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    {family : I → Over X} (hfamily : FpqcCovering family) {K : I → I → Type w}
    {overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom)}
    (hoverlap : ∀ i j, FpqcCovering (overlap i j)) (σ : SchemeOver B)
    (s : (i : I) → (fpMemberFunctor f F family i).obj (op σ)),
    (∃ u, fpCoveringHom f F family hfamily.flat σ u = s) ↔
      fpCoveringPrFst f F family hfamily.flat overlap (fun i j ↦ (hoverlap i j).flat) σ s =
        fpCoveringPrSnd f F family hfamily.flat overlap (fun i j ↦ (hoverlap i j).flat) σ s)

end AlgebraicGeometry.AlgebraicSpace.Quot
