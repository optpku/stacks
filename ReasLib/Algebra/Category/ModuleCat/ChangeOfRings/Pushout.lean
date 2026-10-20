/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.Algebra.Homology.Additive
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Tensor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pushout base change for module objects and complexes

For a pushout square of commutative rings, this leaf identifies extension from `A` to `A'`
followed by restriction to `R'` with extension from `R` to `R'` after restriction to `R`.
The `algebraBaseChange` route retains the `A'`-module structure, while `baseChangeCochain` is the
standard `R' ⊗[R] E` route.  The objectwise comparison is the concrete tensor cancellation; the
functor and complex forms are the reusable downstream interfaces.
@stack 0E1U
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe uR uA uR' uA' w v

namespace CategoryTheory.ModuleCat.Pushout

/-- The two module-level routes around a pushout square. -/
@[stacks 0E1U "pushout base-change route through the target algebra"]
abbrev fromAlgebra
    {A : Type uA} {R' : Type uR'} {A' : Type uA'}
    [CommRing A] [CommRing R'] [CommRing A']
    [Algebra A A'] [Algebra R' A'] :
    ModuleCat.{w, uA} A ⥤ ModuleCat.{max uA' w, uR'} R' :=
    ModuleCat.extendScalars.{uA, uA', w} (algebraMap A A') ⋙
    ModuleCat.restrictScalars.{max uA' w, uR', uA'} (algebraMap R' A')

/-- Extension of scalars along `A → A'`, retaining the resulting `A'`-module structure. -/
@[stacks 0E1U "pushout algebra-valued base-change route"]
abbrev algebraBaseChange
    {A : Type uA} {A' : Type uA'}
    [CommRing A] [CommRing A'] [Algebra A A']
    (E : CochainComplex (ModuleCat.{w, uA} A) ℤ) :
    CochainComplex (ModuleCat.{max uA' w, uA'} A') ℤ :=
  ((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj E

/-- Restrict to the base and then extend along the base change. -/
@[stacks 0E1U "pushout base-change route through the base ring"]
abbrev fromBase
    {R : Type uR} {A : Type uA} {R' : Type uR'}
    [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] :
    ModuleCat.{w, uA} A ⥤ ModuleCat.{max uR' w, uR'} R' :=
  ModuleCat.restrictScalars.{w, uR, uA} (algebraMap R A) ⋙
    ModuleCat.extendScalars.{uR, uR', w} (algebraMap R R')

/-- Concrete cancellation of the two tensor products attached to a pushout square. -/
@[stacks 0E1U "pushout cancellation for module base change"]
noncomputable def moduleIso
    {R : Type uR} {A : Type uA} {R' : Type uR'} {A' : Type uA'}
    [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
    [IsScalarTower R A A'] [IsScalarTower R R' A']
    [Algebra.IsPushout R R' A A']
    (E : ModuleCat.{max uA' uR' w, uA} A) :
    (fromAlgebra (A := A) (R' := R') (A' := A')).obj E ≅
      (fromBase (R := R) (A := A) (R' := R')).obj E :=
  -- These named components are the four canonical tensor cancellations; they keep the
  -- object-level comparison readable and do not rebuild any typeclass instance.
  let MR := (ModuleCat.restrictScalars (algebraMap R A)).obj E
  let e₁ :=
    (ModuleCat.restrictScalars (algebraMap R' A')).mapIso
      (ModuleCat.ExtendScalars.tensorIso (R := A) (S := A') E)
  let e₂ :=
    ModuleCat.RestrictScalars.identityIso (R := R') (S := A')
      (A' ⊗[A] (MR : Type _))
  let e₃ :=
    (Algebra.IsPushout.cancelBaseChange R R' A A' (MR : Type _)).toModuleIso
  let e₄ :=
    (ModuleCat.ExtendScalars.tensorIso (R := R) (S := R')
      MR).symm
  e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄

/-- The forward maps of the pushout comparisons commute with module morphisms. -/
@[stacks 0E1U "naturality of pushout cancellation"]
theorem moduleIso_hom_naturality
    {R : Type uR} {A : Type uA} {R' : Type uR'} {A' : Type uA'}
    [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
    [IsScalarTower R A A'] [IsScalarTower R R' A']
    [Algebra.IsPushout R R' A A']
    {E F : ModuleCat.{max uA' uR' w, uA} A} (f : E ⟶ F) :
    (fromAlgebra (A := A) (R' := R') (A' := A')).map f ≫
        (moduleIso (R := R) (R' := R') (A' := A') F).hom =
      (moduleIso (R := R) (R' := R') (A' := A') E).hom ≫
        (fromBase (R := R) (A := A) (R' := R')).map f := sorry
/- Proof strategy: expand the four tensor cancellations in `moduleIso`, use functoriality of
`ModuleCat.ExtendScalars.tensorIso`, and prove the remaining square by `LinearMap.ext` and tensor
induction, reducing pure tensors with `Algebra.IsPushout.cancelBaseChange_tmul` (and its symmetric
counterpart). -/

/-- The pushout comparison is natural in the module. -/
@[stacks 0E1U "natural pushout cancellation"]
noncomputable def natIso
    {R : Type uR} {A : Type uA} {R' : Type uR'} {A' : Type uA'}
    [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
    [IsScalarTower R A A'] [IsScalarTower R R' A']
    [Algebra.IsPushout R R' A A'] :
    (fromAlgebra (A := A) (R' := R') (A' := A') :
      ModuleCat.{max uA' uR' w, uA} A ⥤ ModuleCat.{max uA' uR' w, uR'} R') ≅
      (fromBase (R := R) (A := A) (R' := R') :
        ModuleCat.{max uA' uR' w, uA} A ⥤ ModuleCat.{max uA' uR' w, uR'} R') :=
  NatIso.ofComponents (moduleIso (R := R) (A := A) (R' := R') (A' := A'))
    (moduleIso_hom_naturality (R := R) (A := A) (R' := R') (A' := A'))

/-- The pushout comparison lifted to homological complexes of any shape. -/
@[stacks 0E1U "pushout cancellation on homological complexes"]
noncomputable def complexNatIso
    {R : Type uR} {A : Type uA} {R' : Type uR'} {A' : Type uA'}
    [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
    [IsScalarTower R A A'] [IsScalarTower R R' A']
    [Algebra.IsPushout R R' A A']
    {ι : Type v} (c : ComplexShape ι) :
    ((fromAlgebra (A := A) (R' := R') (A' := A') :
      ModuleCat.{max uA' uR' w, uA} A ⥤ ModuleCat.{max uA' uR' w, uR'} R').mapHomologicalComplex c) ≅
      ((fromBase (R := R) (A := A) (R' := R') :
        ModuleCat.{max uA' uR' w, uA} A ⥤ ModuleCat.{max uA' uR' w, uR'} R').mapHomologicalComplex c) :=
  NatIso.mapHomologicalComplex natIso c

/-- Objectwise pushout comparison for a homological complex. -/
@[stacks 0E1U "pushout cancellation for homological complexes"]
noncomputable def complexIso
    {R : Type uR} {A : Type uA} {R' : Type uR'} {A' : Type uA'}
    [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
    [IsScalarTower R A A'] [IsScalarTower R R' A']
    [Algebra.IsPushout R R' A A']
    {ι : Type v} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{max uA' uR' w, uA} A) c) :
    (((fromAlgebra (A := A) (R' := R') (A' := A') :
      ModuleCat.{max uA' uR' w, uA} A ⥤ ModuleCat.{max uA' uR' w, uR'} R').mapHomologicalComplex c).obj K) ≅
      (((fromBase (R := R) (A := A) (R' := R') :
        ModuleCat.{max uA' uR' w, uA} A ⥤ ModuleCat.{max uA' uR' w, uR'} R').mapHomologicalComplex c).obj K) :=
  (complexNatIso c).app K

/-- The `up ℤ` specialization of the base-change route on cochain complexes. -/
@[stacks 0E1U "cochain base change through the base ring"]
abbrev baseChangeCochain
    {R : Type uR} {A : Type uA} {R' : Type uR'}
    [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R']
    (E : CochainComplex (ModuleCat.{w, uA} A) ℤ) :
    CochainComplex (ModuleCat.{max uR' w, uR'} R') ℤ :=
  ((fromBase (R := R) (A := A) (R' := R')).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj E

/-- The restricted scalar-extension route on cochain complexes, before the pushout comparison. -/
@[stacks 0E1U "cochain base change through the target algebra"]
abbrev algebraCochain
    {A : Type uA} {R' : Type uR'} {A' : Type uA'}
    [CommRing A] [CommRing R'] [CommRing A']
    [Algebra A A'] [Algebra R' A']
    (E : CochainComplex (ModuleCat.{w, uA} A) ℤ) :
    CochainComplex (ModuleCat.{max uA' w, uR'} R') ℤ :=
  ((ModuleCat.restrictScalars (algebraMap R' A')).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj
    (algebraBaseChange (A := A) (A' := A') E)

/-- After forgetting the `A'`-action, the algebra-valued and standard `R' ⊗[R] E` routes are
canonically isomorphic.  This is the `R'`-linear comparison underlying the source's
`E ⊗[R] R'` notation; the `algebraBaseChange` owner should be used when the `A'`-action matters. -/
@[stacks 0E1U "cochain pushout cancellation"]
noncomputable def cochainIso
    {R : Type uR} {A : Type uA} {R' : Type uR'} {A' : Type uA'}
    [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
    [IsScalarTower R A A'] [IsScalarTower R R' A']
    [Algebra.IsPushout R R' A A']
    (E : CochainComplex (ModuleCat.{max uA' uR' w, uA} A) ℤ) :
    algebraCochain (A := A) (R' := R') (A' := A') E ≅
      baseChangeCochain (R := R) (A := A) (R' := R') E :=
  (complexNatIso (R := R) (A := A) (R' := R') (A' := A')
    (ComplexShape.up ℤ)).app E

end CategoryTheory.ModuleCat.Pushout
