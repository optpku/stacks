/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Topology.RegularLocus
import StacksCheckRecall

/-!
# Definition 28.14.1

The regular and singular loci of a scheme are owned by
`ReasLib.AlgebraicGeometry.Scheme.Topology.RegularLocus`.

@stack 07R1
-/

@[expose] public section

universe u

/- Definition 28.14.1: For a locally Noetherian scheme `X`, the regular locus is the set of
points `x` for which `X.presheaf.stalk x` is a regular local ring, and the singular locus is
its complement, equivalently the set where this condition fails. The canonical definitions
make sense for every scheme. -/
@[stacks 07R1] #check (AlgebraicGeometry.Scheme.regularLocus :
  (X : AlgebraicGeometry.Scheme.{u}) → Set X)

#check (AlgebraicGeometry.Scheme.singularLocus :
  (X : AlgebraicGeometry.Scheme.{u}) → Set X)

#check (AlgebraicGeometry.Scheme.mem_regularLocus :
  (X : AlgebraicGeometry.Scheme.{u}) → (x : X) →
    x ∈ AlgebraicGeometry.Scheme.regularLocus X ↔
      IsRegularLocalRing (X.presheaf.stalk x))

#check (AlgebraicGeometry.Scheme.singularLocus_eq_compl_regularLocus :
  (X : AlgebraicGeometry.Scheme.{u}) →
    AlgebraicGeometry.Scheme.singularLocus X =
      (AlgebraicGeometry.Scheme.regularLocus X)ᶜ)

#check (AlgebraicGeometry.Scheme.compl_regularLocus_eq_singularLocus :
  (X : AlgebraicGeometry.Scheme.{u}) →
    (AlgebraicGeometry.Scheme.regularLocus X)ᶜ =
      AlgebraicGeometry.Scheme.singularLocus X)

#check (AlgebraicGeometry.Scheme.regularLocus_eq_compl_singularLocus :
  (X : AlgebraicGeometry.Scheme.{u}) →
    AlgebraicGeometry.Scheme.regularLocus X =
      (AlgebraicGeometry.Scheme.singularLocus X)ᶜ)

#check (AlgebraicGeometry.Scheme.mem_singularLocus :
  (X : AlgebraicGeometry.Scheme.{u}) → (x : X) →
    x ∈ AlgebraicGeometry.Scheme.singularLocus X ↔
      ¬ IsRegularLocalRing (X.presheaf.stalk x))
