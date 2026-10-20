/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.SteinFactorization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Proper
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

/- Theorem 76.36.5 (Stein factorization; general case) -/
@[stacks 0A1C] #check
  (AlgebraicGeometry.AlgebraicSpace.HasConnectedGeometricFibres.toNormalization_of_proper f :
    AlgebraicGeometry.AlgebraicSpace.HasConnectedGeometricFibres (Hom.toNormalization f))

/- Theorem 76.36.5 (Stein factorization; general case) (1): the canonical
middle space in the factorization is the normalization of `Y` in `X`. -/
@[stacks 0A1C] #check (AlgebraicGeometry.AlgebraicSpace.Hom.normalization f : AlgebraicSpace S)

/- Theorem 76.36.5 (Stein factorization; general case) (2): the canonical maps
through the relative normalization compose to `f`. -/
@[stacks 0A1C] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.toNormalization_fromNormalization f :
    Hom.toNormalization f ≫ Hom.fromNormalization f = f)

/- Theorem 76.36.5 (Stein factorization; general case) (3): the canonical map
from `X` to the relative normalization is proper. -/
@[stacks 0A1C] #check
  (AlgebraicGeometry.AlgebraicSpace.Proper.toNormalization f :
    Proper (Hom.toNormalization f))

/- Theorem 76.36.5 (Stein factorization; general case) (5): the structure
morphism from the relative normalization to `Y` is integral. -/
@[stacks 0A1C] #check
  (AlgebraicGeometry.AlgebraicSpace.IsIntegralHom.fromNormalization f :
    IsIntegralHom (Hom.fromNormalization f))

/- Theorem 76.36.5 (Stein factorization; general case) (6): the structure-sheaf
map of the morphism to the relative normalization is an isomorphism. -/
@[stacks 0A1C] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.instIsIso_commRingStructureSheafMap_toNormalization f :
    IsIso (commStructureSheafMap (Hom.toNormalization f)))

/- Theorem 76.36.5 (Stein factorization; general case) (7): the relative
normalization is uniquely isomorphic over `Y` to
`relativeSpec (pushforwardStructureQcAlgebra f)`. -/
@[stacks 0A1C] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.existsUnique_iso_toPushforwardRelativeSpec f :
    ∃! e : Hom.normalization f ≅ relativeSpec (pushforwardStructureQcAlgebra f),
      Hom.toNormalization f ≫ e.hom = Hom.toPushforwardRelativeSpec f ∧
        e.hom ≫ relativeSpecπ (pushforwardStructureQcAlgebra f) =
          Hom.fromNormalization f)

/- Theorem 76.36.5 (Stein factorization; general case) (8): the constructed
factorization is a relative-normalization factorization. -/
@[stacks 0A1C] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.isNormalization_normalization f :
    IsNormalization f (Hom.toNormalization f) (Hom.fromNormalization f))

end AlgebraicGeometry.AlgebraicSpace
