module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.EtaleNeighborhood
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.41.5: finitely many pairwise distinct isolated points in one fibre of a
separated locally finite type morphism admit an étale base neighbourhood whose pullback
decomposes into finite clopen pieces with singleton distinguished fibres and purely
inseparable residue-field extensions, together with a clopen complement avoiding the
original points. -/
@[stacks 02LO] #check
  (AlgebraicGeometry.Scheme.Hom.exists_clopen_decomposition_purelyInseparable :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsSeparated f]
      (s : S) (n : ℕ) (x : Fin n → X)
      (h_image : ∀ i, f (x i) = s) (h_distinct : Function.Injective x)
      (h_isolated : ∀ i, IsOpen ({f.asFiber (x i)} : Set (f.fiber (f (x i))))),
      ∃ (U : EtaleNeighborhood S s) (m : Fin n → ℕ)
        (D : Option (Σ i, Fin (m i)) → (pullback f U.toEtale.hom).Opens)
        (v : ∀ i j, D (some ⟨i, j⟩)),
        let P := pullback f U.toEtale.hom
        ∃ (_ : iSup D = ⊤)
          (_ : Pairwise (fun a b ↦ Disjoint (D a : Set P) (D b : Set P)))
          (_ : ∀ a, IsClopen (D a : Set P))
          (_ : ∀ i j,
            let V := D (some ⟨i, j⟩)
            let pV := V.ι ≫ pullback.snd f U.toEtale.hom
            let qV := V.ι ≫ pullback.fst f U.toEtale.hom
            ∃ (_ : IsFinite pV)
              (h_point : pV (v i j) = U.point)
              (_ : ∀ w : V, pV w = U.point → w = v i j)
              (_ : qV (v i j) = x i),
              ((Scheme.residueFieldCongr h_point).inv ≫
                pV.residueFieldMap (v i j)).hom.IsPurelyInseparable),
          let W := D none
          let pW := W.ι ≫ pullback.snd f U.toEtale.hom
          let qW := W.ι ≫ pullback.fst f U.toEtale.hom
          ∀ w : W, pW w = U.point → ∀ i, qW w ≠ x i)

end AlgebraicGeometry.Scheme.Hom
