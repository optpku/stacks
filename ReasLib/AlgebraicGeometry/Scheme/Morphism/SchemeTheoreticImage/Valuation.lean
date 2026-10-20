/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiCompact.Specialization
public import ReasLib.AlgebraicGeometry.Scheme.Topology.Valuation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Valuative points of scheme-theoretic images

Every point of the scheme-theoretic image of a quasi-compact morphism is a specialization of an
actual image point. A valuation ring realizing that specialization gives the corresponding
valuative diagram.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A point of the scheme-theoretic image of a quasi-compact morphism admits a valuative
realization whose generic point lifts to the source. -/
@[stacks 02JQ]
theorem exists_valuationRing_diagram_of_mem_schemeTheoreticImage
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (z : Scheme.Hom.image f) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A)
      (K : Type u) (_ : Field K) (_ : Algebra A K) (_ : IsFractionRing A K)
      (genericToX : Spec (CommRingCat.of K) ⟶ X)
      (valuationToImage : Spec (CommRingCat.of A) ⟶ Scheme.Hom.image f),
        CommSq genericToX
          (Spec.map (CommRingCat.ofHom (algebraMap A K)))
          (Scheme.Hom.toImage f) valuationToImage ∧
        valuationToImage (IsLocalRing.closedPoint A) = z := by
  obtain ⟨x, hxz⟩ := (Scheme.Hom.toImage f).exists_specializing_preimage z
  obtain ⟨V, h, hsquare, hclosed⟩ :=
    _root_.Specializes.exists_valuationRing_morphism hxz
      (X.residueField x) ((Scheme.Hom.toImage f).residueFieldMap x)
  refine ⟨V, inferInstance, inferInstance, inferInstance,
    X.residueField x, inferInstance, inferInstance, inferInstance,
    X.fromSpecResidueField x, h, ?_, hclosed⟩
  constructor
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  exact hsquare.w

/-- Every point of the scheme-theoretic image of a quasi-compact morphism is a specialization of
an actual image point. -/
@[stacks 02JQ]
theorem exists_specialization_from_image_of_mem_schemeTheoreticImage
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (z : Scheme.Hom.image f) :
    ∃ x : X, (Scheme.Hom.toImage f) x ⤳ z :=
  (Scheme.Hom.toImage f).exists_specializing_preimage z

end AlgebraicGeometry
