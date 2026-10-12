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

/- Lemma 37.41.2: finitely many isolated points in one fibre of a locally finite type
morphism admit a common elementary etale neighbourhood with finite open pullbacks,
unique points over the distinguished point, and residue-field isomorphisms. -/
@[stacks 02LL] #check
  (AlgebraicGeometry.Scheme.Hom.exists_finiteOpen_etaleNeighborhoods :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (s : S) (n : ℕ) (x : Fin n → X)
      (h_image : ∀ i, f (x i) = s)
      (h_isolated : ∀ i, IsOpen ({f.asFiber (x i)} : Set (f.fiber (f (x i))))),
      ∃ U : EtaleNeighborhood.Elementary S s,
        let E := U.obj
        ∃ (V : Fin n → (pullback f E.toEtale.hom).Opens) (v : ∀ i, V i),
        ∀ i,
          let p := (V i).ι ≫ pullback.snd f E.toEtale.hom
          let q := (V i).ι ≫ pullback.fst f E.toEtale.hom
          ∃ (_ : IsFinite p)
            (_ : ∀ w : V i, p w = E.point ↔ w = v i)
            (hvX : q (v i) = x i),
            IsIso ((X.residueFieldCongr hvX).inv ≫ q.residueFieldMap (v i)))

end AlgebraicGeometry.Scheme.Hom
