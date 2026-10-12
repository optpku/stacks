/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.FundamentalGroup
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory

universe u w

/- Lemma 58.10.6 -/
@[stacks 0BSB] #check
  (AlgebraicGeometry.PuncturedSpectrum.exactSequence_strictHenselization :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] (Ash : Type u)
      [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
      [QuasiCompact (AlgebraicGeometry.PuncturedSpectrum.puncturedOpen A).ι]
      [ConnectedSpace (AlgebraicGeometry.PuncturedSpectrum.scheme Ash)]
      (FX : Scheme.FiniteEtale (Spec (CommRingCat.of A)) ⥤ FintypeCat.{w})
      [GaloisCategory (Scheme.FiniteEtale (Spec (CommRingCat.of A)))]
      [FiberFunctor FX]
      (FU : Scheme.FiniteEtale (AlgebraicGeometry.PuncturedSpectrum.scheme A) ⥤
        FintypeCat.{w})
      [GaloisCategory (Scheme.FiniteEtale (AlgebraicGeometry.PuncturedSpectrum.scheme A))]
      [FiberFunctor FU]
      (FUsh : Scheme.FiniteEtale (AlgebraicGeometry.PuncturedSpectrum.scheme Ash) ⥤
        FintypeCat.{w})
      [GaloisCategory (Scheme.FiniteEtale (AlgebraicGeometry.PuncturedSpectrum.scheme Ash))]
      [FiberFunctor FUsh]
      (D : GaloisFunctorDiagram FX FU FUsh)
      (hU : D.H ≅ Scheme.finiteEtaleBaseChange
        (AlgebraicGeometry.PuncturedSpectrum.puncturedOpen A).ι)
      (hUsh : D.H' ≅ Scheme.finiteEtaleBaseChange
        (AlgebraicGeometry.PuncturedSpectrum.map_strictHenselization Ash)),
      And (Function.Surjective D.h)
        (And (D.h.comp D.h' = 1)
          (MonoidHom.ker D.h.toMonoidHom =
            Subgroup.topologicalClosure
              (Subgroup.normalClosure
                (MonoidHom.range D.h'.toMonoidHom : Set (Aut FU))))))
