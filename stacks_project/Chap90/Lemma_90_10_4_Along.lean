/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.Along

/-!
# Schlessinger's condition (S2) along `squareZero Λ k V`

Condition (S2) is stated for cospans over `A ⟶ k ← dualNumber Λ k`. The same two
clauses, with `dualNumberToResidue Λ k` replaced by `squareZeroToResidue Λ k V`,
are the parameterized property `HasSchlessingerS2Along`.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

variable {F : Type v} [Category.{w} F]

#check (CategoryTheory.Functor.HasSchlessingerS2Along :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) (V : Type u)
    [AddCommGroup V] [Module k V] [Module.Finite k V], Prop)

#check (CategoryTheory.Functor.instHasSchlessingerS2AlongId :
  ∀ (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V],
    HasSchlessingerS2Along (𝟭 (ArtinianLocalAlgCat Λ k)) V)

#check (CategoryTheory.Functor.hasSchlessingerS2Along_spec :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) (V : Type u)
    [AddCommGroup V] [Module k V] [Module.Finite k V],
    HasSchlessingerS2Along p V ↔
      (∀ {x x0 xV : F} (d : x ⟶ x0) (e : xV ⟶ x0),
          p.IsHomLift (squareZeroToResidue Λ k V) e →
            ∃ (y : F) (a : y ⟶ x) (c : y ⟶ xV),
              CommSq a c d e ∧
                IsPullback (p.map a) (p.map c) (p.map d) (p.map e)) ∧
        ∀ {x x0 xV y y' : F} (d : x ⟶ x0) (e : xV ⟶ x0)
            (a : y ⟶ x) (c : y ⟶ xV) (a' : y' ⟶ x) (c' : y' ⟶ xV),
          p.IsHomLift (squareZeroToResidue Λ k V) e →
            CommSq a c d e →
            CommSq a' c' d e →
            IsPullback (p.map a) (p.map c) (p.map d) (p.map e) →
            p.obj y = p.obj y' →
            p.IsHomLift (p.map a) a' →
            p.IsHomLift (p.map c) c' →
              ∃ b : y ⟶ y', p.IsHomLift (𝟙 (p.obj y)) b ∧ b ≫ a' = a)

#check (CategoryTheory.Functor.hasSchlessingerH2_squareZero :
  ∀ (F : ArtinianLocalAlgCat Λ k ⥤ Type v)
    [HasSchlessingerH2 F] {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {A P : ArtinianLocalAlgCat Λ k} (f : A ⟶ residue Λ k)
    (π1 : P ⟶ A) (π2 : P ⟶ squareZero Λ k V)
    (h : IsPullback π1 π2 f (squareZeroToResidue Λ k V)),
    Function.Bijective
      (pullbackObjMap_subtype F π1 π2 f (squareZeroToResidue Λ k V) h))

end CategoryTheory.Functor
