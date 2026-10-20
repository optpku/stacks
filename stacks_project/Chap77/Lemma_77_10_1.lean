/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.Flattening.Local.Subset
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

#check (AlgebraicGeometry.AlgebraicSpace.Modules.flatOverAlongFiberSubset :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (f : X ⟶ ofOver (Over.mk (𝟙 S))) (ℱ : X.Modules) {T : Scheme.{u}}
    (g : T ⟶ S) (t : T) {s : S}
    (E : Set (Points (fiber f s))),
  Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.flatOverAlongFiberSubset_iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (f : X ⟶ ofOver (Over.mk (𝟙 S))) (ℱ : X.Modules) {T : Scheme.{u}}
    (g : T ⟶ S) (t : T) {s : S}
    (E : Set (Points (fiber f s))),
    flatOverAlongFiberSubset f ℱ g t E ↔
      let a := ofOverHomMk g (Category.comp_id g)
      ∀ x : Points (baseChangeSpace f a),
        x ∈ fiberOver (Limits.pullback.snd f a) (ofOver.pointsEquiv (Over.mk g) t) →
          Points.map (Limits.pullback.fst f a) x ∈ Points.map (fiberι f s) '' E →
            flatOverAt (baseChangeModule f a ℱ) (Limits.pullback.snd f a) x)

/- Lemma 77.10.1: over a henselian local affine base, flatness of a finite-type
quasi-coherent module along a subset of the closed fibre is represented by a closed
subscheme. -/
@[stacks 0CWP]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.exists_closedImmersion_over_subset :
  ∀ {S : Scheme.{u}} [IsAffine S]
    [HenselianLocalRing Γ(S, ⊤)] {X : AlgebraicSpace S}
    (f : X ⟶ ofOver (Over.mk (𝟙 S))) [LocallyOfFiniteType f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (s : S) (hs : S.isoSpec.hom s = IsLocalRing.closedPoint Γ(S, ⊤))
    (E : Set (Points (fiber f s))),
    ∃ Z : Over S, AlgebraicGeometry.IsClosedImmersion Z.hom ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S) (t : T) (ht : g t = s),
        flatOverAlongFiberSubset f ℱ g t E ↔
          Nonempty (Over.mk (T.fromSpecStalk t ≫ g) ⟶ Z))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.exists_closedImmersion_over_subset_of_finitePresentation :
  ∀ {S : Scheme.{u}}
    [IsAffine S] [HenselianLocalRing Γ(S, ⊤)] {X : AlgebraicSpace S}
    (f : X ⟶ ofOver (Over.mk (𝟙 S))) [LocallyOfFinitePresentation f]
    (ℱ : X.Modules) [ℱ.IsFinitePresentation]
    (s : S) (hs : S.isoSpec.hom s = IsLocalRing.closedPoint Γ(S, ⊤))
    (E : Set (Points (fiber f s))) (hE_closed : IsClosed E) (hE_compact : IsCompact E),
    ∃ Z : Over S,
      (AlgebraicGeometry.IsClosedImmersion Z.hom ∧ Scheme.Hom.FinitePresentation Z.hom) ∧
        ∀ {T : Scheme.{u}} (g : T ⟶ S) (t : T) (ht : g t = s),
          flatOverAlongFiberSubset f ℱ g t E ↔
            Nonempty (Over.mk (T.fromSpecStalk t ≫ g) ⟶ Z))

end AlgebraicGeometry.AlgebraicSpace.Modules
