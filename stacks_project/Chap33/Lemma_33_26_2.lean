module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.Proper

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 33.26.2: the global-sections algebra of a proper variety over a field is a finite
field extension; geometric reducedness makes it separable, geometric irreducibility makes it
purely inseparable, and geometric integrality makes the canonical base-field map bijective. -/
@[stacks 04L2] #check
  (AlgebraicGeometry.globalSectionsIsField :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsReduced X] [ConnectedSpace X],
      IsField (Scheme.globalSectionsRing X))

#check
  (AlgebraicGeometry.globalSectionsFiniteDimensional :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f],
      FiniteDimensional k (Scheme.Hom.globalSectionsAlg f))

#check
  (AlgebraicGeometry.globalSectionsIsSeparable :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k))
      [IsProper f] [ConnectedSpace X] [GeometricallyReduced f],
      Algebra.IsSeparable k (Scheme.Hom.globalSectionsAlg f))

#check
  (AlgebraicGeometry.globalSectionsIsPurelyInseparable :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k))
      [IsProper f] [IsReduced X] [GeometricallyIrreducible f],
      IsPurelyInseparable k (Scheme.Hom.globalSectionsAlg f))

#check
  (AlgebraicGeometry.globalSectionsAlgebraMapBijectiveOfGeometricallyIntegral :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [GeometricallyIntegral f],
      Function.Bijective (Scheme.Hom.globalSectionsMap f))
