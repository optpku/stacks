module

public import stacks_project.Chap67.Definition_67_48_3_Normalization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.UniversalProperty
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.SteinFactorization
import StacksCheckRecall

/-!
# Stein factorization, Noetherian case

A proper morphism of algebraic spaces to a locally Noetherian target factors
through the relative normalization of the target in the source. The first factor
is proper with connected geometric fibres, the second factor is finite, the
first factor pushes the structure sheaf isomorphically onto the intermediate
structure sheaf, and the intermediate space is identified over the target with
the relative spectrum of the pushed-forward structure sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
  [IsLocallyNoetherian Y] [Proper f]

/- Theorem 76.36.4 (Stein factorization; Noetherian case) -/
@[stacks 0A1B] #check
  (AlgebraicGeometry.AlgebraicSpace.HasConnectedGeometricFibres.toNormalization
    f :
      AlgebraicGeometry.AlgebraicSpace.HasConnectedGeometricFibres
        (AlgebraicGeometry.AlgebraicSpace.Hom.toNormalization f))

/- Theorem 76.36.4 (Stein factorization; Noetherian case) (1): the canonical
middle space in the factorization is the normalization of `Y` in `X`. -/
@[stacks 0A1B] #check (AlgebraicGeometry.AlgebraicSpace.Hom.normalization f : AlgebraicSpace S)

/- Theorem 76.36.4 (Stein factorization; Noetherian case) (2): the canonical maps
through the relative normalization compose to `f`. -/
@[stacks 0A1B] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.toNormalization_fromNormalization f :
    AlgebraicGeometry.AlgebraicSpace.Hom.toNormalization f ≫
        AlgebraicGeometry.AlgebraicSpace.Hom.fromNormalization f = f)

/- Theorem 76.36.4 (Stein factorization; Noetherian case) (3): the canonical map
from `X` to the relative normalization is proper. -/
@[stacks 0A1B] #check
  (AlgebraicGeometry.AlgebraicSpace.Proper.toNormalization f :
    Proper (AlgebraicGeometry.AlgebraicSpace.Hom.toNormalization f))

/- Theorem 76.36.4 (Stein factorization; Noetherian case) (4): the canonical map
from `X` to the relative normalization has connected geometric fibres. -/
@[stacks 0A1B] #check
  (AlgebraicGeometry.AlgebraicSpace.HasConnectedGeometricFibres.toNormalization f :
    AlgebraicGeometry.AlgebraicSpace.HasConnectedGeometricFibres
      (AlgebraicGeometry.AlgebraicSpace.Hom.toNormalization f))

/- Theorem 76.36.4 (Stein factorization; Noetherian case) (5): the structure
morphism from the relative normalization to `Y` is finite. -/
@[stacks 0A1B] #check
  (AlgebraicGeometry.AlgebraicSpace.IsFinite.fromNormalization f :
    IsFinite (AlgebraicGeometry.AlgebraicSpace.Hom.fromNormalization f))

/- Theorem 76.36.4 (Stein factorization; Noetherian case) (6): the structure-sheaf
map of the morphism to the relative normalization is an isomorphism. -/
@[stacks 0A1B] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.instIsIso_commRingStructureSheafMap_toNormalization f :
    IsIso (commStructureSheafMap
      (AlgebraicGeometry.AlgebraicSpace.Hom.toNormalization f)))

/- Theorem 76.36.4 (Stein factorization; Noetherian case) (7): the relative
normalization is uniquely isomorphic over `Y` to `relativeSpec` of the pushed-forward
structure sheaf. -/
@[stacks 0A1B] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.existsUnique_iso_toPushforwardRelativeSpec f :
    ∃! e : AlgebraicGeometry.AlgebraicSpace.Hom.normalization f ≅
        relativeSpec (pushforwardStructureQcAlgebra f),
      AlgebraicGeometry.AlgebraicSpace.Hom.toNormalization f ≫ e.hom =
          AlgebraicGeometry.AlgebraicSpace.Hom.toPushforwardRelativeSpec f ∧
        e.hom ≫ relativeSpecπ (pushforwardStructureQcAlgebra f) =
          AlgebraicGeometry.AlgebraicSpace.Hom.fromNormalization f)

/- Theorem 76.36.4 (Stein factorization; Noetherian case) (8): the constructed
factorization is a relative-normalization factorization. -/
@[stacks 0A1B] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.isNormalization_normalization f :
    IsNormalization f
      (AlgebraicGeometry.AlgebraicSpace.Hom.toNormalization f)
      (AlgebraicGeometry.AlgebraicSpace.Hom.fromNormalization f))

end AlgebraicGeometry.AlgebraicSpace
