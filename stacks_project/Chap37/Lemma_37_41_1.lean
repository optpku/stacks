/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.EtaleNeighborhood
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.41.1: an isolated point in a fibre of a locally finite type morphism has an
elementary étale neighbourhood on which an open part of the base change is finite, has a
unique point above the distinguished point with the same residue field, and retains these
properties after every further elementary étale neighbourhood. -/
@[stacks 02LK] #check
  (AlgebraicGeometry.Scheme.Hom.exists_finiteOpen_etaleNeighborhood :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X),
      IsOpen ({f.asFiber x} : Set (f.fiber (f x))) →
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
                  IsIso ((X.residueFieldCongr hvX').inv ≫ q'.residueFieldMap v'))

end AlgebraicGeometry.Scheme.Hom
