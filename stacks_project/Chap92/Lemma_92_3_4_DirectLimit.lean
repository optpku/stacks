module

public import ReasLib.RingTheory.CotangentComplex.Functoriality
public import ReasLib.RingTheory.CotangentComplex.DirectLimit

@[expose] public section

open CategoryTheory

universe u

/- Commutative squares of ring maps induce maps of scalar-extended cotangent complexes. -/
#check (Algebra.CotangentComplex.map :
  ∀ {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (f' : R' →+* S') (α : R →+* R') (β : S →+* S')
    (hcomm : f'.comp α = β.comp f),
    ((ModuleCat.extendScalars β).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (RingHom.cotangentComplex f) ⟶
      RingHom.cotangentComplex f')
