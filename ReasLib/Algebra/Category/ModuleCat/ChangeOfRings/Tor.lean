/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Projective
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Tensor
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat base change for `Tor`

@stack 00M8

The derived comparison is organized as three reusable identifications: a
source resolution comparison, the monoidal tensor comparison, and a target
resolution comparison.  Their composite is the canonical flat base-change
isomorphism for `Tor`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

noncomputable section

namespace CategoryTheory.ModuleCat.Tor.Flat

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The source-side identification used in flat `Tor` base change: scalar
extension of `Tor` is homology of the scalar-extended tensor resolution. -/
@[stacks 00M8 "flat Tor base change"]
noncomputable def sourceIso
    (f : R →+* S) (hf : f.Flat) (M N : ModuleCat R) (n : ℕ) :
    (ModuleCat.extendScalars f).obj (((CategoryTheory.Tor (ModuleCat R) n).obj M).obj N) ≅
      (HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.down ℕ) n).obj
        (((tensorLeft M ⋙ ModuleCat.extendScalars f).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj (projectiveResolution N).complex) :=
  -- Local instance justification (proof-local temporary data): flatness of `f` canonically
  -- supplies the finite-limit preservation needed by the homology comparison.
  letI : PreservesFiniteLimits (ModuleCat.extendScalars f) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  (ModuleCat.extendScalars f).mapIso ((projectiveResolution N).isoLeftDerivedObj (tensorLeft M) n) ≪≫
    (((((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (projectiveResolution N).complex).sc n).mapHomologyIso
      (ModuleCat.extendScalars f)).symm

/-- The target-side identification used in flat `Tor` base change: the
scalar-extended resolution computes `Tor` after base change. -/
@[stacks 00M8 "flat Tor base change"]
noncomputable def targetIso
    (f : R →+* S) (hf : f.Flat) (M N : ModuleCat R) (n : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.down ℕ) n).obj
      (((ModuleCat.extendScalars f ⋙ tensorLeft ((ModuleCat.extendScalars f).obj M)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj (projectiveResolution N).complex) ≅
    (((CategoryTheory.Tor (ModuleCat S) n).obj ((ModuleCat.extendScalars f).obj M)).obj
      ((ModuleCat.extendScalars f).obj N)) :=
  -- Local instance justification (proof-local temporary data): use the same flatness
  -- witness to transport the selected projective resolution through scalar extension.
  letI : PreservesFiniteLimits (ModuleCat.extendScalars f) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  ((ModuleCat.extendScalars f).mapProjectiveResolution (projectiveResolution N)).isoLeftDerivedObj
    (tensorLeft ((ModuleCat.extendScalars f).obj M)) n |>.symm

/-- Applying homology to the monoidal tensor comparison is the middle
identification in flat `Tor` base change. -/
@[stacks 00M8 "flat Tor base change"]
noncomputable def middleIso
    (f : R →+* S) (M N : ModuleCat R) (n : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.down ℕ) n).obj
      ((Functor.mapHomologicalComplex (tensorLeft M ⋙ ModuleCat.extendScalars f)
          (ComplexShape.down ℕ)).obj (projectiveResolution N).complex) ≅
    (HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.down ℕ) n).obj
      ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars f ⋙ tensorLeft ((ModuleCat.extendScalars f).obj M))
          (ComplexShape.down ℕ)).obj (projectiveResolution N).complex) :=
  (HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.down ℕ) n).mapIso
    ((NatIso.mapHomologicalComplex
      (ModuleCat.ExtendScalars.tensorLeftIso f M) (ComplexShape.down ℕ)).app
        (projectiveResolution N).complex)

/-- The canonical flat base-change isomorphism
`Tor_n^R(M, N) ⊗[R] S ≅ Tor_n^S(M ⊗[R] S, N ⊗[R] S)`. -/
@[stacks 00M8 "flat Tor base change"]
noncomputable def baseChangeIso
    (f : R →+* S) (hf : f.Flat) (M N : ModuleCat R) (n : ℕ) :
    (ModuleCat.extendScalars f).obj (((CategoryTheory.Tor (ModuleCat R) n).obj M).obj N) ≅
      (((CategoryTheory.Tor (ModuleCat S) n).obj ((ModuleCat.extendScalars f).obj M)).obj
        ((ModuleCat.extendScalars f).obj N)) :=
  sourceIso f hf M N n ≪≫ middleIso f M N n ≪≫ targetIso f hf M N n

/-- The canonical morphism underlying the flat `Tor` base-change isomorphism. -/
@[stacks 00M8 "flat Tor base change"]
noncomputable def baseChange
    (f : R →+* S) (hf : f.Flat) (M N : ModuleCat R) (n : ℕ) :
    (ModuleCat.extendScalars f).obj (((CategoryTheory.Tor (ModuleCat R) n).obj M).obj N) ⟶
      (((CategoryTheory.Tor (ModuleCat S) n).obj ((ModuleCat.extendScalars f).obj M)).obj
        ((ModuleCat.extendScalars f).obj N)) :=
  (baseChangeIso f hf M N n).hom

/-- Flat base change makes the canonical comparison morphism on `Tor` an isomorphism. -/
@[stacks 00M8 "flat Tor base change", instance]
theorem baseChange_isIso
    (f : R →+* S) (hf : f.Flat) (M N : ModuleCat R) (n : ℕ) :
    IsIso (baseChange f hf M N n) := by
  change IsIso (baseChangeIso f hf M N n).hom
  infer_instance

end CategoryTheory.ModuleCat.Tor.Flat
