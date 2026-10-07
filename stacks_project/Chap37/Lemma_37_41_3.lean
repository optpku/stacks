module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.EtaleNeighborhood
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.41.3: finitely many distinct isolated points in one fibre of a locally finite type
morphism have an étale base neighbourhood and finite open neighbourhoods whose selected fibre
points are pairwise distinct, exhaustive over the original points, and have finite purely
inseparable residue-field extensions. -/
@[stacks 02LM] #check
  (AlgebraicGeometry.Scheme.Hom.exists_finiteOpen_etaleNeighborhoods_purelyInseparable :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (s : S) (n : ℕ) (x : Fin n → X) (h_image : ∀ i, f (x i) = s)
      (h_injective : Function.Injective x)
      (h_isolated : ∀ i, IsOpen ({f.asFiber (x i)} : Set (f.fiber (f (x i))))),
      ∃ (U : EtaleNeighborhood S s) (m : Fin n → ℕ)
        (V : ∀ i, Fin (m i) → (pullback f U.toEtale.hom).Opens)
        (v : ∀ i j, V i j),
        let P := pullback f U.toEtale.hom
        let p := pullback.snd f U.toEtale.hom
        let q := pullback.fst f U.toEtale.hom
        let pV := fun i j ↦ (V i j).ι ≫ p
        ∃ (h_finite : ∀ i j, IsFinite (pV i j))
          (h_point : ∀ i j, pV i j (v i j) = U.point)
          (h_unique : ∀ i j (w : V i j), pV i j w = U.point → w = v i j)
          (h_residue_finite : ∀ i j,
            ((Scheme.residueFieldCongr (h_point i j)).inv ≫
              (pV i j).residueFieldMap (v i j)).hom.Finite)
          (h_residue_purelyInseparable : ∀ i j,
            ((Scheme.residueFieldCongr (h_point i j)).inv ≫
              (pV i j).residueFieldMap (v i j)).hom.IsPurelyInseparable)
          (h_distinct : Function.Injective (fun a : Σ i, Fin (m i) ↦
            (V a.1 a.2).ι (v a.1 a.2)))
          (h_mapsTo : ∀ i j, q ((V i j).ι (v i j)) = x i),
          ∀ i (w : P), p w = U.point → q w = x i →
            ∃ j, w = (V i j).ι (v i j))

end AlgebraicGeometry.Scheme.Hom
