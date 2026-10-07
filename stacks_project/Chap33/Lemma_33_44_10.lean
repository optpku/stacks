module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.GlobalSections.Degree
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/-
Lemma 33.44.10: the global sections of a proper, reduced, connected scheme over a field form a
finite field extension whose degree divides every vector-bundle degree, closed-point residue
degree, and zero-dimensional closed-subscheme degree.
-/
@[stacks 0C6P] #check
  (AlgebraicGeometry.globalSectionsIsField :
    ∀ {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) [AlgebraicGeometry.IsProper f]
      [AlgebraicGeometry.IsReduced X] [ConnectedSpace X],
      IsField (AlgebraicGeometry.Scheme.globalSectionsRing X))

#check
  (AlgebraicGeometry.globalSectionsFiniteDimensional :
    ∀ {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) [AlgebraicGeometry.IsProper f],
      FiniteDimensional k (AlgebraicGeometry.Scheme.Hom.globalSectionsAlg f))

#check
  (AlgebraicGeometry.SchemeOverField.GlobalSections.finrank :
    ∀ {k : Type u} [Field k], AlgebraicGeometry.SchemeOverField k → ℕ)

#check
  (AlgebraicGeometry.SchemeOverField.GlobalSections.finrank_dvd_curveDegree :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.IsProper X.hom] [AlgebraicGeometry.IsReduced X.left]
      [ConnectedSpace X.left] (hdim : topologicalKrullDim X.left ≤ 1)
      (ℰ : X.left.Modules) (n : ℕ)
      [AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank n ℰ],
      (AlgebraicGeometry.SchemeOverField.GlobalSections.finrank X : ℤ) ∣
        AlgebraicGeometry.Scheme.Modules.curveDegree X.hom hdim ℰ n)

#check
  (AlgebraicGeometry.SchemeOverField.GlobalSections.finrank_dvd_residueFieldDegree :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.IsProper X.hom] [AlgebraicGeometry.IsReduced X.left]
      [ConnectedSpace X.left] (x : closedPoints X.left),
      AlgebraicGeometry.SchemeOverField.GlobalSections.finrank X ∣
        Module.finrank k (X.left.residueField x.1))

#check
  (AlgebraicGeometry.SchemeOverField.GlobalSections.finrank_dvd_zeroDimensionalClosedSubschemeDegree :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.IsProper X.hom] [AlgebraicGeometry.IsReduced X.left]
      [ConnectedSpace X.left] (D : X.left.IdealSheafData)
      (_ : topologicalKrullDim D.subscheme = 0),
      AlgebraicGeometry.SchemeOverField.GlobalSections.finrank X ∣
        Module.finrank k
          (AlgebraicGeometry.Scheme.Hom.globalSectionsAlg (D.subschemeι ≫ X.hom)))
