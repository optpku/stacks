/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.IrreducibleLocal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/- Lemma 33.8.5 (1): geometric irreducibility is equivalent to geometric irreducibility of the
section ring of every nonempty affine open subscheme. -/
@[stacks 038G] #check
  (AlgebraicGeometry.GeometricallyIrreducible.iff_forall_nonempty_affineOpen_sections f :
    AlgebraicGeometry.GeometricallyIrreducible f ↔
      ∀ U : X.affineOpens,
        (U : Set X).Nonempty →
          AlgebraicGeometry.GeometricallyIrreducible.sections f (U : X.Opens))

/- Lemma 33.8.5 (2): geometric irreducibility is equivalent to irreducibility together with an
affine open cover whose section rings are geometrically irreducible. -/
@[stacks 038G] #check
  (AlgebraicGeometry.GeometricallyIrreducible.iff_irreducibleSpace_and_exists_affineOpenCover f :
    AlgebraicGeometry.GeometricallyIrreducible f ↔
      IrreducibleSpace X ∧
        ∃ 𝒰 : X.AffineOpenCover,
          ∀ i : 𝒰.I₀,
            AlgebraicGeometry.GeometricallyIrreducible.sections f (𝒰.f i).opensRange)

/- Lemma 33.8.5 (3): geometric irreducibility is equivalent to the existence of a nonempty open
cover by geometrically irreducible opens with nonempty pairwise intersections. -/
@[stacks 038G] #check
  (AlgebraicGeometry.GeometricallyIrreducible.iff_exists_openCover f :
    AlgebraicGeometry.GeometricallyIrreducible f ↔
      ∃ 𝒰 : Scheme.OpenCover.{u} X,
        Nonempty 𝒰.I₀ ∧
          AlgebraicGeometry.GeometricallyIrreducible.IsOpenCover f 𝒰)

/- Lemma 33.8.5 (4): every nonempty open subscheme of a geometrically irreducible scheme over a
field is geometrically irreducible over that field. -/
@[stacks 038G] #check
  (AlgebraicGeometry.GeometricallyIrreducible.of_nonempty_open f :
    AlgebraicGeometry.GeometricallyIrreducible f →
      ∀ (U : X.Opens), (U : Set X).Nonempty →
        AlgebraicGeometry.GeometricallyIrreducible (U.ι ≫ f))
