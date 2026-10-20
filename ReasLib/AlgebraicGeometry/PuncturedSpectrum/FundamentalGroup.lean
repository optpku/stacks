module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.StrictHenselization
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.PuncturedSpectrum
public import ReasLib.CategoryTheory.GaloisFunctorDiagram

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory

universe u w

namespace AlgebraicGeometry.PuncturedSpectrum

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable (Ash : Type u) [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]

/-- A quasi-compact punctured spectrum with connected punctured spectrum of its
strict henselization induces an exact sequence of automorphism groups of fiber
functors. -/
theorem exactSequence_strictHenselization
    [QuasiCompact (puncturedOpen A).ι]
    [ConnectedSpace (scheme Ash)]
    (FX : Scheme.FiniteEtale (Spec (CommRingCat.of A)) ⥤ FintypeCat.{w})
    [GaloisCategory (Scheme.FiniteEtale (Spec (CommRingCat.of A)))]
    [FiberFunctor FX]
    (FU : Scheme.FiniteEtale (scheme A) ⥤ FintypeCat.{w})
    [GaloisCategory (Scheme.FiniteEtale (scheme A))]
    [FiberFunctor FU]
    (FUsh : Scheme.FiniteEtale (scheme Ash) ⥤ FintypeCat.{w})
    [GaloisCategory (Scheme.FiniteEtale (scheme Ash))]
    [FiberFunctor FUsh]
    (D : GaloisFunctorDiagram FX FU FUsh)
    (hU : D.H ≅ Scheme.finiteEtaleBaseChange (puncturedOpen A).ι)
    (hUsh : D.H' ≅ Scheme.finiteEtaleBaseChange (map_strictHenselization Ash)) :
    Function.Surjective D.h ∧
      D.h.comp D.h' = 1 ∧
      MonoidHom.ker D.h.toMonoidHom =
        (Subgroup.normalClosure
          (MonoidHom.range D.h'.toMonoidHom : Set (Aut FU))).topologicalClosure := sorry

end AlgebraicGeometry.PuncturedSpectrum
