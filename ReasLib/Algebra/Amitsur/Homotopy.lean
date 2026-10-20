/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Amitsur.CosimplicialModule
public import ReasLib.AlgebraicTopology.Cech.Conerve.SplitMono.Homotopy

/-!
# Homotopy contraction of a split Amitsur cosimplicial algebra

An algebra section determines split-monomorphism data for the structural map and hence a
homotopy equivalence from the constant cosimplicial algebra to its Amitsur construction.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace Algebra.Amitsur

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The algebra section identity, expressed in `CommAlgCat R`. -/
theorem section_comp_unit (s : A →ₐ[R] R) :
    CommAlgCat.ofHom (Algebra.ofId R A) ≫ CommAlgCat.ofHom s =
      𝟙 (CommAlgCat.of R R) := sorry

/-- The split monomorphism of commutative `R`-algebras determined by an algebra section. -/
def splitMonoOfSection (s : A →ₐ[R] R) :
    SplitMono (CommAlgCat.ofHom (Algebra.ofId R A)) where
  retraction := CommAlgCat.ofHom s
  id := section_comp_unit s

/-- The retraction in `splitMonoOfSection` is the supplied algebra section. -/
theorem splitMonoOfSection_retraction (s : A →ₐ[R] R) :
    (splitMonoOfSection s).retraction = CommAlgCat.ofHom s := sorry

/-- A section of `R → A` contracts the Amitsur cosimplicial algebra onto the constant
cosimplicial algebra at `R`. -/
noncomputable def homotopyEquivOfSection (s : A →ₐ[R] R) :
    CosimplicialObject.HomotopyEquiv
      ((CosimplicialObject.const (CommAlgCat.{u} R)).obj (CommAlgCat.of R R))
      (cosimplicialAlgebra R A) :=
  SplitMono.cechConerve.coaugmentation.homotopyEquiv (splitMonoOfSection s)

/-- The forward map of the Amitsur contraction is the Čech-conerve coaugmentation. -/
theorem homotopyEquivOfSection_hom (s : A →ₐ[R] R) :
    (homotopyEquivOfSection s).hom =
      (Arrow.mk (CommAlgCat.ofHom (Algebra.ofId R A))).augmentedCechConerve.hom := sorry

/-- The inverse map of the Amitsur contraction is induced degreewise by the section. -/
theorem homotopyEquivOfSection_inv (s : A →ₐ[R] R) :
    (homotopyEquivOfSection s).inv =
      SplitMono.cechConerve.retraction.hom (splitMonoOfSection s) := sorry

end Algebra.Amitsur
