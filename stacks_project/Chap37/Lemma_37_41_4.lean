/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.EtaleNeighborhood
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.41.4: finitely many pairwise distinct isolated points in one fibre of a
separated locally finite type morphism admit an elementary étale neighbourhood whose
pullback decomposes into clopen finite pieces around those points and a complementary
clopen piece avoiding them. -/
@[stacks 02LN] #check
  (AlgebraicGeometry.Scheme.Hom.exists_clopen_decomposition_etaleNeighborhood :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsSeparated f]
      (s : S) (n : ℕ) (x : Fin n → X),
      (∀ i, f (x i) = s) → Function.Injective x →
      (∀ i, IsOpen ({f.asFiber (x i)} : Set (f.fiber (f (x i))))) →
      ∃ U : EtaleNeighborhood.Elementary S s,
        let E := U.obj
        let P := pullback f E.toEtale.hom
        ∃ (D : Option (Fin n) → P.Opens) (v : ∀ i, D (some i))
          (_ : iSup D = ⊤)
          (_ : Pairwise (fun j k ↦ Disjoint (D j : Set P) (D k : Set P)))
          (_ : ∀ j, IsClopen (D j : Set P))
          (_ : ∀ i,
            let V := D (some i)
            let p := V.ι ≫ pullback.snd f E.toEtale.hom
            let q := V.ι ≫ pullback.fst f E.toEtale.hom
            ∃ (_ : IsFinite p)
              (_ : ∀ w : V, p w = E.point ↔ w = v i)
              (hvX : q (v i) = x i),
              IsIso ((X.residueFieldCongr hvX).inv ≫ q.residueFieldMap (v i))),
          let W := D none
          let p := W.ι ≫ pullback.snd f E.toEtale.hom
          let q := W.ι ≫ pullback.fst f E.toEtale.hom
          ∀ w : W, p w = E.point → ∀ i, q w ≠ x i)

end AlgebraicGeometry.Scheme.Hom
