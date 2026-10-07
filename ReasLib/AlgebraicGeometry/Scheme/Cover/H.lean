module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Ph
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# h covering families of schemes

This module defines h covering families in terms of local finite presentation
and proper-hypercovering families.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme

variable {T : Scheme.{u}} {ι : Type v}

/-- An h covering family consists of morphisms locally of finite presentation
which form a `PhCovering`. -/
class HCovering (family : ι → Over T) : Prop where
  /-- Every member of an h covering is locally of finite presentation. -/
  locallyOfFinitePresentation : ∀ i, LocallyOfFinitePresentation (family i).hom
  /-- The underlying family is a `PhCovering`. -/
  toPhCovering :
    AlgebraicGeometry.PhCovering (fun i ↦ (family i).left) (fun i ↦ (family i).hom)

/-- The defining characterization of an h covering family. -/
theorem hCovering_iff (family : ι → Over T) :
    HCovering family ↔
      (∀ i, LocallyOfFinitePresentation (family i).hom) ∧
        AlgebraicGeometry.PhCovering
          (fun i ↦ (family i).left) (fun i ↦ (family i).hom) := sorry

/-- An h covering supplies local finite presentation and the `PhCovering` property. -/
theorem HCovering.source_spec {family : ι → Over T} (hfamily : HCovering family) :
    (∀ i, LocallyOfFinitePresentation (family i).hom) ∧
      AlgebraicGeometry.PhCovering
        (fun i ↦ (family i).left) (fun i ↦ (family i).hom) := sorry

end AlgebraicGeometry.Scheme
