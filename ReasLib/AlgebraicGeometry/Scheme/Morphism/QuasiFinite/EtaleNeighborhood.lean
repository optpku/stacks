/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Pullback.Opens
import Mathlib.RingTheory.Etale.QuasiFinite

/-!
# Elementary étale neighbourhoods of isolated fibre points
-/

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- An isolated point in a fibre of a locally finite type morphism has an elementary étale
neighbourhood on which an open part of the base change is finite, has a unique point above the
distinguished point with the same residue field, and retains these properties after every further
elementary étale neighbourhood. -/
@[stacks 02LK]
theorem exists_finiteOpen_etaleNeighborhood {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X)
    (h_isolated : IsOpen ({f.asFiber x} : Set (f.fiber (f x)))) :
    ∃ U : EtaleNeighborhood.Elementary S (f x),
      let E := U.obj
      ∃ (V : (pullback f E.toEtale.hom).Opens) (v : V),
      let p := V.ι ≫ pullback.snd f E.toEtale.hom
      let q := V.ι ≫ pullback.fst f E.toEtale.hom
      ∃ (_ : IsFinite p)
        (_ : ∀ w : V, p w = E.point ↔ w = v)
        (hvX : q v = x)
        (_ : IsIso ((X.residueFieldCongr hvX).inv ≫ q.residueFieldMap v)),
        ∀ U' : EtaleNeighborhood.Elementary E.toEtale.left E.point,
          let E' := U'.obj
          let g := E'.toEtale.hom
          let φ' := g ≫ E.toEtale.hom
          let k := pullback.map f φ' f E.toEtale.hom
            (𝟙 X) g (𝟙 S)
            ((Category.comp_id f).trans (Category.id_comp f).symm)
            (Category.comp_id φ')
          let V' := k ⁻¹ᵁ V
          ∃ (v' : V'),
            let p' := V'.ι ≫ pullback.snd f φ'
            let q' := V'.ι ≫ pullback.fst f φ'
            ∃ (_ : IsFinite p')
              (_ : ∀ w' : V', p' w' = E'.point ↔ w' = v')
              (hvX' : q' v' = x),
              IsIso ((X.residueFieldCongr hvX').inv ≫ q'.residueFieldMap v') := sorry

/-- A finite family of isolated points in one fibre of a locally finite type morphism admits a
common elementary étale neighbourhood with finite open pullbacks, unique points over the
distinguished point, and isomorphisms on residue fields. -/
@[stacks 02LL]
theorem exists_finiteOpen_etaleNeighborhoods {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (s : S) (n : ℕ) (x : Fin n → X)
    (h_image : ∀ i, f (x i) = s)
    (h_isolated : ∀ i, IsOpen ({f.asFiber (x i)} : Set (f.fiber (f (x i))))) :
    ∃ U : EtaleNeighborhood.Elementary S s,
      let E := U.obj
      ∃ (V : Fin n → (pullback f E.toEtale.hom).Opens) (v : ∀ i, V i),
      ∀ i,
        let p := (V i).ι ≫ pullback.snd f E.toEtale.hom
        let q := (V i).ι ≫ pullback.fst f E.toEtale.hom
        ∃ (_ : IsFinite p)
          (_ : ∀ w : V i, p w = E.point ↔ w = v i)
          (hvX : q (v i) = x i),
          IsIso ((X.residueFieldCongr hvX).inv ≫ q.residueFieldMap (v i)) := sorry

/-- Finitely many distinct isolated points in one fibre of a locally finite type morphism have,
after an étale base neighbourhood, finite open neighbourhoods whose unique selected fibre points
exhaust the points above each original point and induce finite purely inseparable residue-field
extensions. -/
@[stacks 02LM]
theorem exists_finiteOpen_etaleNeighborhoods_purelyInseparable
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (s : S) (n : ℕ) (x : Fin n → X) (h_image : ∀ i, f (x i) = s)
    (h_injective : Function.Injective x)
    (h_isolated : ∀ i, IsOpen ({f.asFiber (x i)} : Set (f.fiber (f (x i))))) :
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
          ∃ j, w = (V i j).ι (v i j) := sorry

/-- Finitely many distinct isolated points in one fibre of a separated locally finite type
morphism admit an elementary étale base neighbourhood whose pullback decomposes into pairwise
disjoint clopen pieces: a finite piece with one distinguished-fibre point and unchanged residue
field for each selected point, and a complementary piece avoiding all selected points. -/
@[stacks 02LN]
theorem exists_clopen_decomposition_etaleNeighborhood {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsSeparated f] (s : S) (n : ℕ) (x : Fin n → X)
    (h_image : ∀ i, f (x i) = s) (h_distinct : Function.Injective x)
    (h_isolated : ∀ i, IsOpen ({f.asFiber (x i)} : Set (f.fiber (f (x i))))) :
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
        ∀ w : W, p w = E.point → ∀ i, q w ≠ x i := sorry

/-- Finitely many distinct isolated points in one fibre of a separated locally finite type
morphism admit, after an étale base neighbourhood, a pairwise disjoint clopen decomposition into
finite pieces with singleton distinguished fibres and purely inseparable residue-field extensions,
together with a complementary piece avoiding the selected points. -/
@[stacks 02LO]
theorem exists_clopen_decomposition_purelyInseparable {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsSeparated f] (s : S) (n : ℕ) (x : Fin n → X)
    (h_image : ∀ i, f (x i) = s) (h_distinct : Function.Injective x)
    (h_isolated : ∀ i, IsOpen ({f.asFiber (x i)} : Set (f.fiber (f (x i))))) :
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
        ∀ w : W, pW w = U.point → ∀ i, qW w ≠ x i := sorry

/-- After an elementary étale base change, a separated locally finite type morphism with
finitely many isolated points in the distinguished fibre decomposes into a finite clopen part
and a clopen part whose distinguished fibre has no isolated points. -/
@[stacks 02LP]
theorem exists_clopen_decomposition_noIsolatedFiber {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsSeparated f] (s : S)
    (h_isolated : Set.Finite
      {x : f.fiber s | IsOpen ({x} : Set (f.fiber s))}) :
    ∃ U : EtaleNeighborhood.Elementary S s,
      let E := U.obj
      let P := pullback f E.toEtale.hom
      ∃ (W V : P.Opens)
        (_ : W ⊔ V = ⊤)
        (_ : Disjoint (W : Set P) (V : Set P))
        (_ : IsClopen (W : Set P))
        (_ : IsClopen (V : Set P)),
        let pV := V.ι ≫ pullback.snd f E.toEtale.hom
        let pW := W.ι ≫ pullback.snd f E.toEtale.hom
        ∃ (_ : IsFinite pV),
          ∀ w : pW.fiber E.point,
            ¬ IsOpen ({w} : Set (pW.fiber E.point)) := sorry

/-- If the point-set fibre of a separated locally finite type morphism is finite, then after an
elementary étale base change it decomposes into a finite clopen part and a clopen part with empty
distinguished fibre. -/
@[stacks 02LP]
theorem exists_clopen_decomposition_emptyFiber_of_finite {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsSeparated f] (s : S)
    (h_finite : Set.Finite (f ⁻¹' ({s} : Set S))) :
    ∃ U : EtaleNeighborhood.Elementary S s,
      let E := U.obj
      let P := pullback f E.toEtale.hom
      ∃ (W V : P.Opens)
        (_ : W ⊔ V = ⊤)
        (_ : Disjoint (W : Set P) (V : Set P))
        (_ : IsClopen (W : Set P))
        (_ : IsClopen (V : Set P)),
        let pV := V.ι ≫ pullback.snd f E.toEtale.hom
        let pW := W.ι ≫ pullback.snd f E.toEtale.hom
        ∃ (_ : IsFinite pV), IsEmpty (pW.fiber E.point) := sorry

end AlgebraicGeometry.Scheme.Hom
