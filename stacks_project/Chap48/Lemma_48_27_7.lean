/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.FieldChange

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 48.27.7
If a proper scheme over a field factors through the spectrum of another field, the chosen
proper dualizing complex and dualizing module agree with those of the factored morphism; after
a field extension, their pullbacks agree with the canonical objects of the base change.
-/
@[stacks 0FW1]
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.ofFieldFactorization :
    ∀ {k k' : Type u} [Field k] [Field k'] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (f' : X ⟶ Spec (CommRingCat.of k')) [IsProper f']
    (g : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k))
    (hfactor : f' ≫ g = f),
    IsIsomorphic (AlgebraicGeometry.Scheme.DerivedQCoh.properDualizingComplex f)
      (AlgebraicGeometry.Scheme.DerivedQCoh.properDualizingComplex f') ∧
      IsIsomorphic
        (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.dualizingModule f)
        (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.dualizingModule f'))

#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.isProper_ofFieldFactorization :
    ∀ {k k' : Type u} [Field k] [Field k'] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (f' : X ⟶ Spec (CommRingCat.of k'))
    (g : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k))
    (hfactor : f' ≫ g = f), IsProper f')

#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.baseChange :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f],
    let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
    IsIsomorphic
        ((AlgebraicGeometry.Scheme.DerivedQCoh.pullback (pullback.fst f g)).obj
          (AlgebraicGeometry.Scheme.DerivedQCoh.properDualizingComplex f))
        (AlgebraicGeometry.Scheme.DerivedQCoh.properDualizingComplex (pullback.snd f g)) ∧
      IsIsomorphic
        ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.fst f g)).obj
          (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.dualizingModule f))
        (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.dualizingModule
          (pullback.snd f g)))
