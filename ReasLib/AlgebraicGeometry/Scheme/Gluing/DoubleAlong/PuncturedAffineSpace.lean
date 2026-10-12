/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedAffineSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong.QuasiSeparated
import Mathlib.Tactic.CrossRefAttribute

/-!
# Affine space with its zero section doubled

This module specializes the general doubling construction to the complement
of the zero section in affine space.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedAffineSpace.DoubleAlong

section CommRing

variable (ι : Type u) (k : Type u) [CommRing k]

/-- Affine space doubled along its punctured open. -/
@[stacks 01KL "doubled punctured affine space"]
noncomputable abbrev scheme : Scheme.{u} :=
  Scheme.doubleAlong (PuncturedAffineSpace.puncturedOpen ι k)

/-- The open immersion of the `i`-th copy of affine space into the doubled scheme. -/
@[stacks 01KL "doubled punctured affine chart map"]
noncomputable abbrev chartMap (i : Fin 2) :
    PuncturedAffineSpace.affineSpace ι k ⟶ scheme ι k :=
  Scheme.DoubleAlong.chartMap (PuncturedAffineSpace.puncturedOpen ι k) i

/-- One of the two canonical affine-space charts. -/
@[stacks 01KL "doubled punctured affine chart"]
abbrev chart (i : Fin 2) : (scheme ι k).Opens :=
  Scheme.DoubleAlong.chart (PuncturedAffineSpace.puncturedOpen ι k) i

/-- The canonical identification of a doubled punctured-affine chart with affine space. -/
@[stacks 01KL "doubled punctured affine chart isomorphism"]
noncomputable abbrev chartIso (i : Fin 2) :
    (chart ι k i).toScheme ≅ PuncturedAffineSpace.affineSpace ι k :=
  Scheme.DoubleAlong.chartIso (PuncturedAffineSpace.puncturedOpen ι k) i

/-- The two canonical charts cover the doubled scheme. -/
@[stacks 01KL "doubled punctured affine chart cover"]
theorem chart_cover : chart ι k 0 ⊔ chart ι k 1 = ⊤ := sorry

/-- Every canonical chart is affine. -/
@[stacks 01KL "doubled punctured affine charts"]
theorem chart_isAffineOpen (i : Fin 2) : IsAffineOpen (chart ι k i) := sorry

/-- The punctured affine space mapped into the doubled scheme through the first chart. -/
@[stacks 01KL "doubled punctured affine overlap map"]
noncomputable abbrev overlapMap :
    (PuncturedAffineSpace.puncturedOpen ι k).toScheme ⟶ scheme ι k :=
  Scheme.DoubleAlong.overlapMap (PuncturedAffineSpace.puncturedOpen ι k)

/-- The image of the punctured-affine-space overlap is the intersection of the two canonical
charts. -/
@[simp, stacks 01KL "doubled punctured-affine overlap range"]
theorem overlapMap_opensRange :
    (overlapMap ι k).opensRange = chart ι k 0 ⊓ chart ι k 1 := sorry

/-- The punctured-affine-space overlap embeds through either canonical chart. -/
@[stacks 01KL "doubled punctured-affine overlap identification", reassoc]
theorem overlapMap_eq_secondChart :
    overlapMap ι k =
      (PuncturedAffineSpace.puncturedOpen ι k).ι ≫ chartMap ι k 1 := sorry

/-- The fold morphism from the doubled scheme to affine space. -/
@[stacks 01KL "doubled punctured affine fold"]
noncomputable abbrev fold : scheme ι k ⟶ PuncturedAffineSpace.affineSpace ι k :=
  Scheme.DoubleAlong.fold (PuncturedAffineSpace.puncturedOpen ι k)

/-- The restriction of the fold from a canonical chart to affine space. -/
@[stacks 01KL "doubled punctured affine chart comparison"]
noncomputable abbrev chartComparison (i : Fin 2) :
    (chart ι k i).toScheme ⟶ PuncturedAffineSpace.affineSpace ι k :=
  (chartIso ι k i).hom

/-- The fold restricts to the identity on each affine-space chart. -/
@[reassoc (attr := simp), stacks 01KL "doubled punctured affine fold on charts"]
theorem chartMap_fold (i : Fin 2) : chartMap ι k i ≫ fold ι k = 𝟙 _ := sorry

/-- The structure morphism from the doubled scheme to `Spec k`. -/
@[stacks 01KL "doubled punctured affine structure morphism"]
noncomputable abbrev toBase : scheme ι k ⟶ Spec (CommRingCat.of k) :=
  fold ι k ≫ PuncturedAffineSpace.toBase ι k

/-- The canonical map from the polynomial coordinate ring to global sections of affine space
doubled along its punctured open, induced by the fold. -/
@[stacks 01KL "doubled punctured-affine global-sections comparison"]
noncomputable abbrev globalSectionsComparison :
    CommRingCat.of (PuncturedAffineSpace.coordinateRing ι k) ⟶
      Scheme.Γ.obj (Opposite.op (scheme ι k)) :=
  PuncturedAffineSpace.coordinateRingToGlobalSections ι k ≫
    Scheme.Γ.map (fold ι k).op

namespace globalSectionsComparison

/-- A chosen coordinate is a fine-grained witness that the fold induces an isomorphism on global
sections. -/
@[stacks 01KL "global sections from a coordinate"]
theorem isIso_of_coordinate (i : ι) :
    IsIso (globalSectionsComparison ι k) := sorry

/-- For a nonempty coordinate family, the fold induces an isomorphism on global sections. This
remains an ordinary theorem while its proof is deferred, so no inverse is selected from typeclass
search. -/
@[stacks 01KL "global sections of doubled punctured affine space"]
theorem isIso [Nonempty ι] :
    IsIso (globalSectionsComparison ι k) := sorry

end globalSectionsComparison

end CommRing

section Field

variable (ι : Type u) (k : Type u) [Field k]

/-- The origin in the `i`-th canonical chart. -/
@[stacks 01KL "the doubled origins"]
noncomputable abbrev origin (i : Fin 2) : scheme ι k :=
  Scheme.DoubleAlong.point (PuncturedAffineSpace.puncturedOpen ι k) i
    (PuncturedAffineSpace.origin ι k)

/-- Each origin lies in its corresponding affine chart. -/
@[stacks 01KL "doubled punctured affine origin membership"]
theorem origin_mem_chart (i : Fin 2) : origin ι k i ∈ chart ι k i := sorry

/-- The two origins in the doubled scheme are distinct. -/
@[stacks 01KL "doubled punctured affine distinct origins"]
theorem origin_ne : origin ι k 0 ≠ origin ι k 1 := sorry

/-- Folding either origin gives the ordinary affine-space origin. -/
@[simp, stacks 01KL "doubled punctured affine fold on origins"]
theorem fold_origin (i : Fin 2) :
    (fold ι k).base (origin ι k i) = PuncturedAffineSpace.origin ι k := sorry

/-- A chosen coordinate witnesses that the doubled-origin scheme is not affine. -/
@[stacks 01KL "doubled punctured affine nonaffineness witness"]
theorem not_isAffine_of_coordinate (i : ι) : ¬ IsAffine (scheme ι k) := sorry

/-- If the coordinate family is nonempty, its doubled-origin scheme is not affine. -/
@[stacks 01KL "nonaffineness of doubled punctured affine space"]
theorem not_isAffine [Nonempty ι] : ¬ IsAffine (scheme ι k) := sorry

/-- A chosen coordinate witnesses that the doubled-origin scheme is not separated. -/
@[stacks 01KL "doubled punctured affine nonseparatedness witness"]
theorem not_isSeparated_of_coordinate (i : ι) : ¬ (scheme ι k).IsSeparated := sorry

/-- If the coordinate family is nonempty, its doubled-origin scheme is not separated. -/
@[stacks 01KL "nonseparated doubled punctured affine space",
  stacks 0FXT "affine space with doubled origin is not separated"]
theorem not_isSeparated [Nonempty ι] : ¬ (scheme ι k).IsSeparated := sorry

/-- Two chosen distinct coordinates witness that the intersection of the canonical charts is not
affine. -/
@[stacks 01KL "doubled punctured affine nonaffine overlap witness"]
theorem chart_inf_not_isAffineOpen_of_coordinates (i j : ι) (hij : i ≠ j) :
    ¬ IsAffineOpen (chart ι k 0 ⊓ chart ι k 1) := sorry

/-- If the coordinate family is nontrivial, the intersection of the canonical charts is not
affine. -/
@[stacks 01KL "nonaffine overlap of doubled punctured affine space"]
theorem chart_inf_not_isAffineOpen [Nontrivial ι] :
    ¬ IsAffineOpen (chart ι k 0 ⊓ chart ι k 1) := sorry

end Field

section Infinite

variable (ι : Type u) [Infinite ι] (k : Type u) [CommRing k] [Nontrivial k]

/-- For infinitely many coordinates, the fold is not quasi-separated. -/
@[stacks 01KL]
theorem fold_not_quasiSeparated : ¬ QuasiSeparated (fold ι k) := sorry

/-- The mixed-chart overlap immersion is not quasi-compact. -/
@[stacks 01KL]
theorem overlap_not_quasiCompact :
    ¬ QuasiCompact ((chart ι k 0 ⊓ chart ι k 1).ι) := sorry

/-- The named overlap morphism is not quasi-compact.  This is the morphism-level form of the
intersection statement above, so consumers of `overlapMap` need not transport the property
through `overlapMap_opensRange` themselves. -/
@[stacks 01KL "doubled punctured affine overlap morphism is not quasi-compact"]
theorem overlapMap_not_quasiCompact :
    ¬ QuasiCompact (overlapMap ι k) := sorry

/-- The mixed-chart overlap is not compact as a subset of the doubled scheme. -/
@[stacks 01KL "doubled punctured affine noncompact overlap"]
theorem overlap_not_isCompact :
    ¬ IsCompact (((chart ι k 0 ⊓ chart ι k 1 : (scheme ι k).Opens)) :
      Set (scheme ι k)) := sorry

/-- With infinitely many coordinates, the structure morphism of the doubled-origin scheme is
not quasi-separated. -/
@[stacks 01KL]
theorem toBase_not_quasiSeparated : ¬ QuasiSeparated (toBase ι k) := sorry

end Infinite

end AlgebraicGeometry.PuncturedAffineSpace.DoubleAlong
