/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic.Core
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.ResidueChange
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Scheme

/-!
# Residue-field restriction of a fibre object over `Spec(k)`

A finite field extension `k → l` produces `Spec(l) ⟶ S`, the restriction `x_{l,0}` of an
object over `Spec(k)`, and the morphism `Spec(B) ⟶ Spec(B ×_l k)` in `Over S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open ArtinianLocalAlgCat

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable (k l : Type u) [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Field l] [Algebra Λ l] [Module.Finite Λ l]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
variable (X : GroupoidsOver S) (x0 : X.p.Fiber (Over.mk kToS))

/-- The morphism `Spec(l) ⟶ Spec(k)` induced by a finite field extension `k → l`. -/
def residueHom : Spec (CommRingCat.of l) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k l))

/-- `residueHom` is `Spec` of the structure map `k → l`. -/
theorem residueHom_eq : residueHom k l = Spec.map (CommRingCat.ofHom (algebraMap k l)) :=
  sorry

/-- The structure morphism `Spec(l) ⟶ S` obtained by composing `residueHom` with `kToS`. -/
def lToS : Spec (CommRingCat.of l) ⟶ S :=
  residueHom k l ≫ kToS

/-- `lToS` is the composite `Spec(l) ⟶ Spec(k) ⟶ S`. -/
theorem lToS_comp : lToS k l kToS = residueHom k l ≫ kToS :=
  sorry

/-- The finite extension `k → l` is compatible with the chosen affine open `Spec(Λ) ⊂ S`. -/
theorem lToS_factor
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS) :
    Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ openImmersion = lToS k l kToS :=
  sorry

/-- The morphism `Over.mk lToS ⟶ Over.mk kToS` with left component `residueHom`. -/
def residueOverHom : Over.mk (lToS k l kToS) ⟶ Over.mk kToS :=
  Over.homMk (residueHom k l) rfl

/-- `residueOverHom` has left component `residueHom`. -/
theorem residueOverHom_left : (residueOverHom k l kToS).left = residueHom k l :=
  sorry

/-- `Spec(l) ⟶ S` is locally of finite type, as a finite composite of finite-type morphisms. -/
instance instLocallyOfFiniteType_lToS : LocallyOfFiniteType (lToS k l kToS) :=
  sorry

/-- The restriction `x_{l,0}` of `x0` to `Spec(l)`, selected by the cleavage of `𝒳`. -/
def restrictResidue : X.p.Fiber (Over.mk (lToS k l kToS)) :=
  Chosen.reindexObj X.p (residueOverHom k l kToS) x0

/-- `restrictResidue` lies over `Spec(l) ⟶ S`, and its cartesian arrow lifts `residueOverHom`. -/
theorem restrictResidue_spec :
    X.p.obj (Fiber.fiberInclusion.obj (restrictResidue k l kToS X x0)) =
        Over.mk (lToS k l kToS) ∧
      X.p.IsHomLift (residueOverHom k l kToS)
        (Chosen.cartesianHom X.p (residueOverHom k l kToS) x0) :=
  sorry

/-- Compatibility of `Spec.map residueChangeFst` with the two structure morphisms to `S`. -/
theorem specOverResidueChange_comp (B : ArtinianLocalAlgCat Λ l) :
    Spec.map (CommRingCat.ofHom (residueChangeFst k B).toRingHom) ≫
        (specOver openImmersion (residueChange k B)).hom =
      (specOver openImmersion B).hom :=
  sorry

/-- The morphism `Spec(B) ⟶ Spec(B ×_l k)` over `S` induced by the first algebra projection. -/
def specOverResidueChange (B : ArtinianLocalAlgCat Λ l) :
    specOver openImmersion B ⟶ specOver openImmersion (residueChange k B) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (residueChangeFst k B).toRingHom))
    (specOverResidueChange_comp k l openImmersion B)

/-- `specOverResidueChange B` is `Spec` of `residueChangeFst`, as a morphism of `Over S`. -/
theorem specOverResidueChange_spec (B : ArtinianLocalAlgCat Λ l) :
    (specOverResidueChange k l openImmersion B).left =
        Spec.map (CommRingCat.ofHom (residueChangeFst k B).toRingHom) ∧
      Spec.map (CommRingCat.ofHom (residueChangeFst k B).toRingHom) ≫
          (specOver openImmersion (residueChange k B)).hom =
        (specOver openImmersion B).hom :=
  sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
