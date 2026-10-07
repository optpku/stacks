module

public import stacks_project.Chap99.Lemma_99_3_5_Equalizer

/-!
# Lemma 99.3.5

In Situation 99.3.1, Hom-values of quasi-coherent modules on an algebraic
space are recovered as the equalizer of the Čech parallel pair associated
with an fppf covering of the total space and fppf coverings of the fibre
products of covering members.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 99.3.5: in Situation 99.3.1, an fppf covering `{X_i ⟶ X}` together
with fppf coverings `{X_ijk ⟶ X_i ×_X X_j}` presents `Hom(F, G)(T)` as the
equalizer of the two restrictions
`∏_i Hom(F_i, G_i)(T) ⇉ ∏_{i,j,k} Hom(F_ijk, G_ijk)(T)`
for every scheme `T` over `B`. -/
@[stacks 08K3]
theorem homFunctor_covering_equalizer {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    {ι : Type v} {Xi : ι → AlgebraicSpace S} (fi : (i : ι) → Xi i ⟶ X)
    [FppfCovering Xi fi] {κ : ι → ι → Type w}
    {Xijk : (i j : ι) → κ i j → AlgebraicSpace S}
    (g : (i j : ι) → (k : κ i j) → Xijk i j k ⟶ Limits.pullback (fi i) (fi j))
    [∀ i j, FppfCovering (Xijk i j) (g i j)] (σ : SchemeOver B)
    (s : (i : ι) →
      (homFunctor (fi i ≫ f) ((pullback (fi i)).obj F)
        ((pullback (fi i)).obj G)).obj (op σ))
    (hs : coveringPrFst f F G fi g σ s = coveringPrSnd f F G fi g σ s) :
    ∃! u, coveringHom f F G fi σ u = s :=
  sorry

/-- The restriction map `Hom(F, G)(T) ⟶ ∏_i Hom(F_i, G_i)(T)` is injective. -/
theorem homFunctor_covering_injective {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    {ι : Type v} {Xi : ι → AlgebraicSpace S} (fi : (i : ι) → Xi i ⟶ X)
    [FppfCovering Xi fi] {κ : ι → ι → Type w}
    {Xijk : (i j : ι) → κ i j → AlgebraicSpace S}
    (g : (i j : ι) → (k : κ i j) → Xijk i j k ⟶ Limits.pullback (fi i) (fi j))
    [∀ i j, FppfCovering (Xijk i j) (g i j)] (σ : SchemeOver B) :
    Function.Injective (coveringHom f F G fi σ) :=
  sorry

/-- A family in `∏_i Hom(F_i, G_i)(T)` comes from `Hom(F, G)(T)` if and only if
it is equalized by `pr₀^*` and `pr₁^*`. -/
theorem coveringHom_eq_iff {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    {ι : Type v} {Xi : ι → AlgebraicSpace S} (fi : (i : ι) → Xi i ⟶ X)
    [FppfCovering Xi fi] {κ : ι → ι → Type w}
    {Xijk : (i j : ι) → κ i j → AlgebraicSpace S}
    (g : (i j : ι) → (k : κ i j) → Xijk i j k ⟶ Limits.pullback (fi i) (fi j))
    [∀ i j, FppfCovering (Xijk i j) (g i j)] (σ : SchemeOver B)
    (s : (i : ι) →
      (homFunctor (fi i ≫ f) ((pullback (fi i)).obj F)
        ((pullback (fi i)).obj G)).obj (op σ)) :
    (∃ u, coveringHom f F G fi σ u = s) ↔
      coveringPrFst f F G fi g σ s = coveringPrSnd f F G fi g σ s :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
