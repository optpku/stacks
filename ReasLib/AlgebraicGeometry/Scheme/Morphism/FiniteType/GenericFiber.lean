/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.Scheme.Reduction.Functor
import Mathlib.Tactic.CrossRefAttribute
import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiCompact.GenericPointAvoidance

/-!
# Generic fibers of finite-type morphisms

This file relates empty and nonempty generic fibers to the behavior of a finite-type morphism
over an open subscheme of an irreducible target.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.FiniteType

/-- A finite-type morphism to an irreducible scheme with nonempty generic fiber is surjective
after restriction to some nonempty open subscheme of the target. -/
@[stacks 05F5]
theorem exists_open_surjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] [IrreducibleSpace Y]
    (hη : Nonempty (f.fiber (genericPoint Y))) :
    ∃ V : Y.Opens, Nonempty V ∧ Surjective (f ∣_ V) := sorry

/-- A finite-type morphism to an irreducible scheme with empty generic fiber has empty base
change over some nonempty open subscheme of the target. -/
@[stacks 054W]
theorem exists_open_of_isEmpty_genericFiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] [IrreducibleSpace Y]
    (hfiber : IsEmpty (f.fiber (genericPoint Y))) :
    ∃ V : Y.Opens, Nonempty V ∧ IsEmpty (Limits.pullback V.ι f : Scheme) := sorry

/-- After restricting a finite-type morphism to an irreducible base to a nonempty open,
there is a finite universal homeomorphism from an integral affine scheme such that the
reduced pullback is flat and finitely presented with geometrically reduced generic fibre;
its map to the restricted source is also finite and a universal homeomorphism. -/
@[stacks 0550]
theorem exists_finiteUniversalHomeomorphism_geometricallyReducedGenericFiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] [IrreducibleSpace Y] :
    ∃ (V : Y.Opens) (_ : Nonempty V) (Y' : Scheme.{u}) (g : Y' ⟶ V)
      (_ : IsFinite g) (_ : UniversalHomeomorphism g) (_ : IsIntegral Y') (_ : IsAffine Y'),
      let X_V := pullback V.ι f
      let pV : X_V ⟶ V := pullback.fst V.ι f
      let jV : X_V ⟶ X := pullback.snd V.ι f
      let P := pullback g pV
      let X' := Scheme.reduction P
      let f' : X' ⟶ Y' := Scheme.reductionι P ≫ pullback.fst g pV
      let g' : X' ⟶ X_V := Scheme.reductionι P ≫ pullback.snd g pV
      ∃ (_ : CommSq jV pV f V.ι) (_ : CommSq g' f' pV g)
        (_ : IsFinite g') (_ : UniversalHomeomorphism g') (_ : Flat f')
        (_ : Scheme.Hom.FinitePresentation f'),
        GeometricallyReduced (f'.fiberToSpecResidueField (genericPoint Y')) := sorry

/-- After restricting a finite-type morphism to an irreducible base to a nonempty open,
there is a surjective finite étale cover by an irreducible affine scheme such that every
irreducible component of the generic fibre of the resulting base change is geometrically
irreducible. -/
@[stacks 0551]
theorem exists_finiteEtaleCover_geometricallyIrreducibleGenericFiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] [IrreducibleSpace Y] :
    ∃ (V : Y.Opens) (_ : Nonempty V) (Y' : Scheme.{u}) (g : Y' ⟶ V)
      (_ : Surjective g) (_ : IsFinite g) (_ : Etale g)
      (_ : IsAffine Y') (_ : IrreducibleSpace Y'),
      GeometricallyIrreducible.Components.all
        ((Limits.pullback.fst g (Limits.pullback.fst V.ι f)).fiberToSpecResidueField
          (genericPoint Y')) := sorry

end AlgebraicGeometry.Scheme.Hom.FiniteType
