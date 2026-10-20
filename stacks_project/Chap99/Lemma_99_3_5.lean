module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HomFunctor.Covering
import StacksCheckRecall

/-!
# Lemma 99.3.5

Hom-values of quasi-coherent modules are the equalizer of restriction to an
fppf covering and the parallel restrictions to refined pairwise overlaps.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 99.3.5: the restriction diagram is an equalizer. -/
@[stacks 08K3] #check (AlgebraicGeometry.AlgebraicSpace.Modules.homFunctor_covering_equalizer :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    {ι : Type v} {Xi : ι → AlgebraicSpace S} (fi : (i : ι) → Xi i ⟶ X)
    [FppfCovering Xi fi] {κ : ι → ι → Type w}
    {Xijk : (i j : ι) → κ i j → AlgebraicSpace S}
    (g : (i j : ι) → (k : κ i j) → Xijk i j k ⟶ Limits.pullback (fi i) (fi j))
    [∀ i j, FppfCovering (Xijk i j) (g i j)] (σ : SchemeOver B),
    (∀ u, coveringPrFst f F G fi g σ (coveringHom f F G fi σ u) =
      coveringPrSnd f F G fi g σ (coveringHom f F G fi σ u)) ∧
    (∀ s : (i : ι) →
      (homFunctor (fi i ≫ f) ((pullback (fi i)).obj F)
        ((pullback (fi i)).obj G)).obj (op σ),
      coveringPrFst f F G fi g σ s = coveringPrSnd f F G fi g σ s →
        ∃! u, coveringHom f F G fi σ u = s))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.homFunctor_covering_injective :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    {ι : Type v} {Xi : ι → AlgebraicSpace S} (fi : (i : ι) → Xi i ⟶ X)
    [FppfCovering Xi fi] {κ : ι → ι → Type w}
    {Xijk : (i j : ι) → κ i j → AlgebraicSpace S}
    (g : (i j : ι) → (k : κ i j) → Xijk i j k ⟶ Limits.pullback (fi i) (fi j))
    [∀ i j, FppfCovering (Xijk i j) (g i j)] (σ : SchemeOver B),
    Function.Injective (coveringHom f F G fi σ))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.coveringHom_eq_iff :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    {ι : Type v} {Xi : ι → AlgebraicSpace S} (fi : (i : ι) → Xi i ⟶ X)
    [FppfCovering Xi fi] {κ : ι → ι → Type w}
    {Xijk : (i j : ι) → κ i j → AlgebraicSpace S}
    (g : (i j : ι) → (k : κ i j) → Xijk i j k ⟶ Limits.pullback (fi i) (fi j))
    [∀ i j, FppfCovering (Xijk i j) (g i j)] (σ : SchemeOver B)
    (s : (i : ι) →
      (homFunctor (fi i ≫ f) ((pullback (fi i)).obj F)
        ((pullback (fi i)).obj G)).obj (op σ)),
    (∃ u, coveringHom f F G fi σ u = s) ↔
      coveringPrFst f F G fi g σ s = coveringPrSnd f F G fi g σ s)

end AlgebraicGeometry.AlgebraicSpace.Modules
