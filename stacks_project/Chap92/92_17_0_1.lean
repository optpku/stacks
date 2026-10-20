module

public import ReasLib.RingTheory.CotangentComplex.Atiyah.Triangle
import StacksCheckRecall

universe u

open CategoryTheory CategoryTheory.Pretriangulated

/- 92.17.0.1: for a ring map A → B and a B-module M, the functorial first
principal-parts sequence on C_{B/A} yields a distinguished triangle in D(B)
Algebra.CotangentComplex.Atiyah.tensorModule ⟶
Algebra.CotangentComplex.Atiyah.derivedPrincipalParts ⟶
M ⟶ (Algebra.CotangentComplex.Atiyah.tensorModule)⟦1⟧. -/
@[stacks 09DD]
#check (Algebra.CotangentComplex.Atiyah.triangle_distinguished :
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (M : ModuleCat.{u} B),
    Algebra.CotangentComplex.Atiyah.triangle A B M ∈
      distTriang (DerivedCategory (ModuleCat.{u} B)))

#check Algebra.CotangentComplex.Atiyah.triangle
#check Algebra.CotangentComplex.Atiyah.tensorModule
#check Algebra.CotangentComplex.Atiyah.derivedPrincipalParts
#check Algebra.CotangentComplex.Atiyah.tensorToPrincipalParts
#check Algebra.CotangentComplex.Atiyah.principalPartsToModule
#check Algebra.CotangentComplex.Atiyah.connectingMap
