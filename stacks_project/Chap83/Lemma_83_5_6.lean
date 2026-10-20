/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Generated
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits
open _root_.Relation (EqvGen)

noncomputable section

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
variable (P : PreRelation U)

/- Lemma 83.5.6 (1), tag 048T: the generated pre-relation is a pre-equivalence relation. -/
@[stacks 048T] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.generated_isPreEquivalence P :
    P.generated.IsPreEquivalence)

/- Lemma 83.5.6 (2), tag 048T: invariance agrees for the original and generated relations. -/
@[stacks 048T] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.equalizes_iff_generated P :
    ∀ {X : Over B} (φ : U ⟶ X), P.IsInvariantHom φ ↔ P.generated.IsInvariantHom φ)

/- Lemma 83.5.6 (3), tag 048T: the canonical fppf quotient-sheaf map is an isomorphism. -/
@[stacks 048T] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.generated_spacesQuotientMap_isIso P :
    IsIso P.generated_spacesQuotientMap)

/- Lemma 83.5.6 (4), tag 048T: weak orbits agree on geometric points. -/
@[stacks 048T] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.generated_eqvGen_pointRel P :
    ∀ (k : GeometricPoint B) (x y : Over.mk k.hom ⟶ U),
      EqvGen (P.pointRel (Over.mk k.hom)) x y ↔
        EqvGen (P.generated.pointRel (Over.mk k.hom)) x y)

/- Lemma 83.5.6 (5), tag 048T: orbits agree after field extension. -/
@[stacks 048T] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.generated_orbitRel P :
    ∀ (k : GeometricPoint B) (x y : Over.mk k.hom ⟶ U),
      (∃ (L : Type u) (_ : Field L) (_ : Algebra k.K L),
          EqvGen (P.pointRel (Over.mk (fieldExtensionOverMap L k.structureHom ≫ k.hom)))
            (restrictAlongFieldExtension L x) (restrictAlongFieldExtension L y)) ↔
        (∃ (L : Type u) (_ : Field L) (_ : Algebra k.K L),
          EqvGen (P.generated.pointRel
              (Over.mk (fieldExtensionOverMap L k.structureHom ≫ k.hom)))
            (restrictAlongFieldExtension L x) (restrictAlongFieldExtension L y)))

/- Lemma 83.5.6 (6), tag 048T: both projections remain locally of finite type. -/
@[stacks 048T] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.instLocallyOfFiniteType_generated_s P :
    [LocallyOfFiniteType P.s.left] → [LocallyOfFiniteType P.t.left] →
      LocallyOfFiniteType P.generated.s.left)

#check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.instLocallyOfFiniteType_generated_t P :
    [LocallyOfFiniteType P.s.left] → [LocallyOfFiniteType P.t.left] →
      LocallyOfFiniteType P.generated.t.left)
