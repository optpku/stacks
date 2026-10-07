module

public import stacks_project.Chap67.Definition_67_48_3_Normalization
public import stacks_project.Chap67.Lemma_67_48_5_Normalization
public import stacks_project.Chap76.Lemma_76_36_1_Instances
public import stacks_project.Chap76.Theorem_76_36_4_Stein_factorization_Noetherian_case_GeometricallyConnected
public import stacks_project.Chap76.Theorem_76_36_4_Stein_factorization_Noetherian_case_Instances
import StacksCheckRecall

/-!
# Stein factorization, Noetherian case

A proper morphism of algebraic spaces to a locally Noetherian target factors
through the relative normalization of the target in the source. The first factor
is proper with connected geometric fibres, the second factor is finite, the
first factor pushes the structure sheaf isomorphically onto the intermediate
structure sheaf, and the intermediate space is uniquely identified over the
target with the relative spectrum of the pushed-forward structure sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
  [IsLocallyNoetherian Y] [Proper f]

/- Theorem 76.36.4 (Stein factorization; Noetherian case) (1): the canonical
middle space in the factorization is the normalization of `Y` in `X`. -/
@[stacks 0A1B] #check (Hom.normalization f : AlgebraicSpace S)

/- Theorem 76.36.4 (Stein factorization; Noetherian case) (2): the canonical maps
through the relative normalization compose to `f`. -/
@[stacks 0A1B] #check
  (Hom.toNormalization_fromNormalization f :
    Hom.toNormalization f ≫ Hom.fromNormalization f = f)

/- Theorem 76.36.4 (Stein factorization; Noetherian case) (3): the canonical map
from `X` to the relative normalization is proper. -/
@[stacks 0A1B] #check
  (Hom.instProper_toNormalization f : Proper (Hom.toNormalization f))

/- Theorem 76.36.4 (Stein factorization; Noetherian case) (4): the canonical map
from `X` to the relative normalization has connected geometric fibres. -/
@[stacks 0A1B] #check
  (Hom.instHasConnectedGeometricFibres_toNormalization f :
    Hom.HasConnectedGeometricFibres (Hom.toNormalization f))

/- Theorem 76.36.4 (Stein factorization; Noetherian case) (5): the structure
morphism from the relative normalization to `Y` is finite. -/
@[stacks 0A1B] #check
  (Hom.instIsFinite_fromNormalization f : IsFinite (Hom.fromNormalization f))

/- Theorem 76.36.4 (Stein factorization; Noetherian case) (6): the structure-sheaf
map of the morphism to the relative normalization is an isomorphism. -/
@[stacks 0A1B] #check
  (Hom.instIsIso_commRingStructureSheafMap_toNormalization f :
    IsIso (commRingStructureSheafMap (Hom.toNormalization f)))

/- Theorem 76.36.4 (Stein factorization; Noetherian case) (7): the relative
normalization is uniquely isomorphic over `Y` to
`relativeSpec (pushforwardStructureQcAlgebra f)`. -/
@[stacks 0A1B] #check
  (Hom.existsUnique_iso_toPushforwardRelativeSpec f :
    ∃! e : Hom.normalization f ≅ relativeSpec (pushforwardStructureQcAlgebra f),
      Hom.toNormalization f ≫ e.hom = Hom.toPushforwardRelativeSpec f ∧
        e.hom ≫ relativeSpecπ (pushforwardStructureQcAlgebra f) =
          Hom.fromNormalization f)

/- Theorem 76.36.4 (Stein factorization; Noetherian case) (8): the constructed
factorization is a relative-normalization factorization. -/
@[stacks 0A1B] #check
  (Hom.isNormalization_normalization f :
    IsNormalization f (Hom.toNormalization f) (Hom.fromNormalization f))

end AlgebraicGeometry.AlgebraicSpace
