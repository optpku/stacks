module

public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Stein.FiniteType
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 37.53.2 (1): the fibre of the relative-normalization morphism over any point of
the base is finite. -/
@[stacks 0E0M] #check
  (AlgebraicGeometry.Scheme.Hom.fromNormalization_fiberFinite :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [QuasiSeparated f] [UniversallyClosed f] [LocallyOfFiniteType f]
      (s : S),
      Set.Finite (f.fromNormalization.pointsOver s))

/- Lemma 37.53.2 (2): every point in a fibre of the relative-normalization morphism has
residue field finite over the residue field of the base point. -/
@[stacks 0E0M] #check
  (AlgebraicGeometry.Scheme.Hom.instModuleFiniteResidueFieldFromNormalization :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [QuasiSeparated f] [UniversallyClosed f] [LocallyOfFiniteType f]
      (s : S) (s' : f.fromNormalization.pointsOver s),
      Module.Finite (S.residueField s) (f.normalization.residueField s'))
