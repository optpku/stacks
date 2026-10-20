/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Tensor.HomologicalComplex
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.BaseChange.NatRestriction
public import ReasLib.RingTheory.DividedPowers.Tate.Tor

/-!
# Tor computed after explicit base change of a Tate resolution

A Tate resolution computes `Tor` in Mathlib's derived second variable.  Given an explicit
base-change model of its divided-power chain DGA, restriction of scalars identifies that Tor
complex with the restricted natural complex of the model.  No resolution or base-change model
is chosen in this file.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace TateResolution.BaseChange

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]
variable {J : Type v} {pi0 : MvPolynomial J R →ₐ[R] T}
variable (A : TateResolution.{u, v} pi0)

/-- The natural complex of an explicit base-change model, regarded again as a complex of
`R`-modules. -/
abbrev restrictedComplex
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) :
    ChainComplex (ModuleCat R) ℕ :=
  ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj X.algebra.toChainDGAlgebra.natRestriction

/-- Tag 09PQ: the tensor complex computing `Tor` is canonically isomorphic to the restricted
natural complex of a supplied base-change model. -/
@[stacks 09PQ "Tate Tor complex after explicit base change"]
noncomputable def complexIso
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) :
    A.tensorComplex (ModuleCat.of R S) ≅ restrictedComplex A X :=
  (ModuleCat.ExtendScalars.restrictTensorComplexIso
      (S := S) A.naturalComplex).symm ≪≫
    ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex
      (ComplexShape.down ℕ)).mapIso
        (DividedPowerChainAlgebra.BaseChange.NatRestriction.complexIso X)

/-- The component of `complexIso` is the composite of the inverse tensor normalization and
the restricted degreewise base-change comparison. -/
@[simp]
theorem complexIso_app
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) (n : ℕ) :
    HomologicalComplex.Hom.isoApp (complexIso A X) n =
      (ModuleCat.ExtendScalars.restrictTensorIso
          (R := R) (S := S) (A.naturalComplex.X n)).symm ≪≫
        (ModuleCat.restrictScalars (algebraMap R S)).mapIso
          (DividedPowerChainAlgebra.BaseChange.NatRestriction.pieceModuleIso X n) := sorry

/-- The forward chain map from the Tate tensor complex to the restricted base-change model. -/
noncomputable def complexHom
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) :
    A.tensorComplex (ModuleCat.of R S) ⟶ restrictedComplex A X :=
  (complexIso A X).hom

/-- The inverse chain map from the restricted base-change model to the Tate tensor complex. -/
noncomputable def complexInv
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) :
    restrictedComplex A X ⟶ A.tensorComplex (ModuleCat.of R S) :=
  (complexIso A X).inv

/-- Tag 09PQ: a supplied base-change model computes the canonical Tor object after restriction
to the base ring. -/
@[stacks 09PQ "Tor computed by an explicit base-change model"]
noncomputable def homologyIso
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) (n : ℕ) :
    (((CategoryTheory.Tor (ModuleCat R) n).obj (ModuleCat.of R S)).obj
        (ModuleCat.of R T)) ≅
      (restrictedComplex A X).homology n :=
  A.torIso (ModuleCat.of R S) n ≪≫
    HomologicalComplex.homologyMapIso (complexIso A X) n

/-- The forward Tor comparison is the Tate-resolution comparison followed by the homology map
of `complexHom`. -/
theorem homologyIso_hom
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) (n : ℕ) :
    (homologyIso A X n).hom =
      (A.torIso (ModuleCat.of R S) n).hom ≫
        HomologicalComplex.homologyMap (complexHom A X) n := sorry

/-- Restrict the canonical natural-complex comparison between two supplied base-change models. -/
@[stacks 09PQ "comparison of restricted Tate base-change complexes"]
def comparisonComplexIso
    (X Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) :
    restrictedComplex A X ≅ restrictedComplex A Y :=
  ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex
    (ComplexShape.down ℕ)).mapIso
      (DividedPowerChainAlgebra.BaseChange.NatRestriction.comparisonComplexIso X Y)

/-- The forward restricted-complex comparison is restriction of the canonical divided-power
chain-DGA comparison. -/
@[simp]
theorem comparisonComplexIso_hom
    (X Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) :
    (comparisonComplexIso A X Y).hom =
      ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex
        (ComplexShape.down ℕ)).map
          ((X.chainComparison Y).toChainHom.natRestriction) := sorry

/-- The inverse restricted-complex comparison is restriction of the reverse canonical
divided-power chain-DGA comparison. -/
@[simp]
theorem comparisonComplexIso_inv
    (X Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) :
    (comparisonComplexIso A X Y).inv =
      ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex
        (ComplexShape.down ℕ)).map
          ((Y.chainComparison X).toChainHom.natRestriction) := sorry

/-- The restricted model comparison is equivalently obtained by passing through the canonical
Tate tensor complex. -/
theorem comparisonComplexIso_eq
    (X Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) :
    comparisonComplexIso A X Y =
      (complexIso A X).symm.trans (complexIso A Y) := sorry

/-- The canonical restricted-complex comparison from a model to itself is reflexive. -/
@[simp]
theorem comparisonComplexIso_self
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) :
    comparisonComplexIso A X X = Iso.refl (restrictedComplex A X) := sorry

/-- Reversing the canonical restricted-complex comparison exchanges its two models. -/
@[simp]
theorem comparisonComplexIso_symm
    (X Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) :
    (comparisonComplexIso A X Y).symm = comparisonComplexIso A Y X := sorry

/-- Canonical restricted-complex comparisons compose transitively. -/
@[simp]
theorem comparisonComplexIso_trans
    (X Y Z : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) :
    (comparisonComplexIso A X Y).trans (comparisonComplexIso A Y Z) =
      comparisonComplexIso A X Z := sorry

/-- The Tor complex comparison is independent of the supplied base-change model up to the
canonical model comparison. -/
theorem complexIso_naturality
    (X Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) :
    (complexIso A X).trans (comparisonComplexIso A X Y) = complexIso A Y := sorry

/-- Restriction of the canonical model comparison induces the corresponding homology
isomorphism. -/
@[stacks 09PQ "comparison of restricted Tate base-change homology"]
noncomputable def comparisonHomologyIso
    (X Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) (n : ℕ) :
    (restrictedComplex A X).homology n ≅
      (restrictedComplex A Y).homology n :=
  HomologicalComplex.homologyMapIso (comparisonComplexIso A X Y) n

/-- The forward homology comparison is induced by the forward restricted-complex
comparison. -/
@[simp]
theorem comparisonHomologyIso_hom
    (X Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) (n : ℕ) :
    (comparisonHomologyIso A X Y n).hom =
      HomologicalComplex.homologyMap (comparisonComplexIso A X Y).hom n := sorry

/-- The inverse homology comparison is induced by the inverse restricted-complex
comparison. -/
@[simp]
theorem comparisonHomologyIso_inv
    (X Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) (n : ℕ) :
    (comparisonHomologyIso A X Y n).inv =
      HomologicalComplex.homologyMap (comparisonComplexIso A X Y).inv n := sorry

/-- The model comparison on homology is equivalently obtained by passing through canonical
`Tor`. -/
theorem comparisonHomologyIso_eq
    (X Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) (n : ℕ) :
    comparisonHomologyIso A X Y n =
      (homologyIso A X n).symm.trans (homologyIso A Y n) := sorry

/-- The canonical homology comparison from a model to itself is reflexive. -/
@[simp]
theorem comparisonHomologyIso_self
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) (n : ℕ) :
    comparisonHomologyIso A X X n =
      Iso.refl ((restrictedComplex A X).homology n) := sorry

/-- Reversing the canonical homology comparison exchanges its two models. -/
@[simp]
theorem comparisonHomologyIso_symm
    (X Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) (n : ℕ) :
    (comparisonHomologyIso A X Y n).symm =
      comparisonHomologyIso A Y X n := sorry

/-- Canonical homology comparisons compose transitively. -/
@[simp]
theorem comparisonHomologyIso_trans
    (X Y Z : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) (n : ℕ) :
    (comparisonHomologyIso A X Y n).trans
        (comparisonHomologyIso A Y Z n) =
      comparisonHomologyIso A X Z n := sorry

/-- The Tor-to-model homology comparison is natural under canonical comparison of supplied
base-change models. -/
theorem homologyIso_naturality
    (X Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) (n : ℕ) :
    (homologyIso A X n).trans (comparisonHomologyIso A X Y n) =
      homologyIso A Y n := sorry

/-- Forward Tor-to-model maps commute with the canonical comparison of supplied base-change
models. -/
theorem homologyIso_hom_naturality
    (X Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) (n : ℕ) :
    (homologyIso A X n).hom ≫ (comparisonHomologyIso A X Y n).hom =
      (homologyIso A Y n).hom := sorry

/-- Inverse Tor-to-model maps commute with the canonical comparison of supplied base-change
models. -/
theorem homologyIso_inv_naturality
    (X Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) (n : ℕ) :
    (comparisonHomologyIso A X Y n).hom ≫ (homologyIso A Y n).inv =
      (homologyIso A X n).inv := sorry

end TateResolution.BaseChange
