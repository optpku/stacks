module

public import stacks_project.Chap67.Definition_67_48_3_Normalization
public import stacks_project.Chap67.Lemma_67_48_5_Normalization
public import stacks_project.Chap76.Lemma_76_36_1_Instances
public import stacks_project.Chap76.Theorem_76_36_4_Stein_factorization_Noetherian_case_GeometricallyConnected
public import stacks_project.Chap76.Theorem_76_36_4_Stein_factorization_Noetherian_case_Instances
public import stacks_project.Chap76.Theorem_76_36_5_Stein_factorization_general_case_Instances
import StacksCheckRecall

/-!
# Stein factorization, general case

A proper morphism of algebraic spaces factors through the relative
normalization of the target in the source. The first factor is proper with
connected geometric fibres, the second factor is integral, the first factor
pushes the structure sheaf isomorphically onto the intermediate structure
sheaf, and the intermediate space is uniquely identified over the target with
the relative spectrum of the pushed-forward structure sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]

/- Theorem 76.36.5 (Stein factorization; general case) (1): the canonical
middle space in the factorization is the normalization of `Y` in `X`. -/
@[stacks 0A1C] #check (Hom.normalization f : AlgebraicSpace S)

/- Theorem 76.36.5 (Stein factorization; general case) (2): the canonical maps
through the relative normalization compose to `f`. -/
@[stacks 0A1C] #check
  (Hom.toNormalization_fromNormalization f :
    Hom.toNormalization f ≫ Hom.fromNormalization f = f)

/- Theorem 76.36.5 (Stein factorization; general case) (3): the canonical map
from `X` to the relative normalization is proper. -/
@[stacks 0A1C] #check
  (Hom.instProper_toNormalization f : Proper (Hom.toNormalization f))

/- Theorem 76.36.5 (Stein factorization; general case) (4): the canonical map
from `X` to the relative normalization has connected geometric fibres. -/
@[stacks 0A1C] #check
  (Hom.instHasConnectedGeometricFibres_toNormalization_of_proper f :
    Hom.HasConnectedGeometricFibres (Hom.toNormalization f))

/- Theorem 76.36.5 (Stein factorization; general case) (5): the structure
morphism from the relative normalization to `Y` is integral. -/
@[stacks 0A1C] #check
  (Hom.instIsIntegralHom_fromNormalization f :
    IsIntegralHom (Hom.fromNormalization f))

/- Theorem 76.36.5 (Stein factorization; general case) (6): the structure-sheaf
map of the morphism to the relative normalization is an isomorphism. -/
@[stacks 0A1C] #check
  (Hom.instIsIso_commRingStructureSheafMap_toNormalization f :
    IsIso (commRingStructureSheafMap (Hom.toNormalization f)))

/- Theorem 76.36.5 (Stein factorization; general case) (7): the relative
normalization is uniquely isomorphic over `Y` to
`relativeSpec (pushforwardStructureQcAlgebra f)`. -/
@[stacks 0A1C] #check
  (Hom.existsUnique_iso_toPushforwardRelativeSpec f :
    ∃! e : Hom.normalization f ≅ relativeSpec (pushforwardStructureQcAlgebra f),
      Hom.toNormalization f ≫ e.hom = Hom.toPushforwardRelativeSpec f ∧
        e.hom ≫ relativeSpecπ (pushforwardStructureQcAlgebra f) =
          Hom.fromNormalization f)

/- Theorem 76.36.5 (Stein factorization; general case) (8): the constructed
factorization is a relative-normalization factorization. -/
@[stacks 0A1C] #check
  (Hom.isNormalization_normalization f :
    IsNormalization f (Hom.toNormalization f) (Hom.fromNormalization f))

end AlgebraicGeometry.AlgebraicSpace
