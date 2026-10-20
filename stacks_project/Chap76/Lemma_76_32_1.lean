/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Integral.Glueing
import StacksCheckRecall

/-!
# Glueing factorization of an integral morphism at a closed point

An integral morphism factors through the relative spectrum of an algebra pullback
at a closed field-valued point. The first factor is an isomorphism away from the
fibre, which has exactly one point with residue field the given field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.32.1: the glueing factorization is integral, is an isomorphism away
from the distinguished fibre, has a singleton fibre with the given residue field,
and is finite when the original morphism is finite over a locally Noetherian target. -/
@[stacks 0EDM] #check
  (AlgebraicGeometry.AlgebraicSpace.IsIntegralHom.fromGlueing :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f]
      (p : FieldValuedPoint Y) [IsClosedImmersion p.hom],
      IsIntegralHom (fromGlueing f p))

#check (AlgebraicGeometry.AlgebraicSpace.isIso_openInverseImageTo_toGlueing :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f]
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] {U : AlgebraicSpace S}
    (ι : U ⟶ glueingSpec f p) [IsOpenImmersion ι]
    (hU : Set.range (Points.map ι) =
      (Set.range (Points.map (fieldFiberι (fromGlueing f p) p)))ᶜ),
    IsIso (openInverseImageTo (toGlueing f p) ι))

#check (AlgebraicGeometry.AlgebraicSpace.existsUnique_fiberPoint_eq_residueField :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f]
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom],
    ∃ x' : Points (fieldFiber (fromGlueing f p) p),
      (∀ z : Points (fieldFiber (fromGlueing f p) p), z = x') ∧
      ∃ σ : ofOver p.overObj ⟶ fieldFiber (fromGlueing f p) p,
        σ ≫ fieldFiberToSpec (fromGlueing f p) p = 𝟙 (ofOver p.overObj) ∧
          Points.mk (FieldValuedPoint.of p.K p.structureHom σ) = x')

#check (AlgebraicGeometry.AlgebraicSpace.IsFinite.fromGlueing :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsFinite f] [IsLocallyNoetherian Y]
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom],
    IsFinite (fromGlueing f p))

#check (AlgebraicGeometry.AlgebraicSpace.toGlueing_comp_fromGlueing :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f]
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom],
    toGlueing f p ≫ fromGlueing f p = f)
