module

public import ReasLib.AlgebraicGeometry.Scheme.Topology.Constructible
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open Topology
open scoped Set.Notation

universe u

/- Lemma 28.2.1: a subset of a scheme is locally constructible if and only if its trace on every
affine open subscheme is constructible. -/
@[stacks 054C] #check
  (AlgebraicGeometry.Scheme.isLocallyConstructible_iff_forall_isAffineOpen :
    ∀ {X : Scheme.{u}} {E : Set X}, IsLocallyConstructible E ↔
      ∀ U : X.Opens, IsAffineOpen U → IsConstructible ((U : Set X) ↓∩ E))

#check
  (AlgebraicGeometry.Scheme.IsLocallyConstructible.isConstructible_affineOpen :
    ∀ {X : Scheme.{u}} {E : Set X}, IsLocallyConstructible E →
      ∀ U : X.affineOpens, IsConstructible ((U : Set X) ↓∩ E))
