/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Free.Presentation
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.QuasiIso.Basic
public import ReasLib.Algebra.Homology.CochainDGAlgebra.KFlat
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Free K-Flat Resolutions of Cochain Differential Graded Algebras

This leaf owns the bundled data and existence theorem for a quasi-isomorphic
K-flat replacement whose underlying graded algebra has a free word-basis
presentation.
-/

open CategoryTheory
open CategoryTheory.MorphismProperty

noncomputable section

universe u v w

namespace CochainDGAlgebra.Free

variable {R : Type u} [CommRing R]

/-- A free K-flat resolution of a cochain differential graded algebra is a quasi-isomorphism
from a K-flat cochain differential graded algebra with a free graded-algebra presentation. -/
@[stacks 0BZ7 "free K-flat resolution"]
structure KFlatResolution (B : CochainDGAlgebra.{u, v} R) where
  /-- The resolving cochain differential graded algebra. -/
  complex : CochainDGAlgebra.{u, v} R
  /-- The comparison map from the resolving algebra to the target. -/
  π : CochainDGAlgebra.Hom complex B
  /-- The resolving graded algebra has a free word-basis presentation. -/
  presentation : Presentation.{u, v, w} complex
  /-- The comparison map is a quasi-isomorphism of cochain differential graded algebras. -/
  quasiIso : CochainDGAlgebra.quasiIso π
  /-- The resolving algebra is K-flat. -/
  isKFlat : complex.IsKFlat

namespace KFlatResolution

/-- A free K-flat resolution can be used as its resolving cochain differential graded algebra. -/
@[stacks 0BZ7 "coercion from a free K-flat resolution to its DGA"]
instance {B : CochainDGAlgebra.{u, v} R} :
    CoeOut (KFlatResolution.{u, v, w} B) (CochainDGAlgebra.{u, v} R) where
  coe P := P.complex

/-- The underlying cochain map of a free K-flat resolution is a quasi-isomorphism. -/
@[stacks 0BZ7 "quasi-isomorphism underlying a free K-flat resolution"]
instance {B : CochainDGAlgebra.{u, v} R} (P : KFlatResolution.{u, v, w} B) :
    _root_.QuasiIso P.π.toCochainMap := P.quasiIso

/-- A freely presented K-flat cochain differential graded algebra resolves itself. -/
@[stacks 0BZ7 "self-resolution from a free K-flat presentation"]
noncomputable def self {B : CochainDGAlgebra.{u, v} R}
    (P : Presentation.{u, v, w} B) (hB : B.IsKFlat) :
    KFlatResolution.{u, v, w} B :=
  { complex := B
    π := 𝟙 B
    presentation := P
    quasiIso := (CochainDGAlgebra.quasiIso (R := R)).id_mem B
    isKFlat := hB }

/-- The resolving DGA of the canonical self-resolution is the original DGA. -/
@[simp, stacks 0BZ7 "complex of the canonical self-resolution"]
theorem self_complex {B : CochainDGAlgebra.{u, v} R}
    (P : Presentation.{u, v, w} B) (hB : B.IsKFlat) :
    (self P hB).complex = B := sorry

/-- The comparison map of the canonical self-resolution is the identity. -/
@[simp, stacks 0BZ7 "comparison map of the canonical self-resolution"]
theorem self_π {B : CochainDGAlgebra.{u, v} R}
    (P : Presentation.{u, v, w} B) (hB : B.IsKFlat) :
    (self P hB).π = 𝟙 B := sorry

/-- The canonical self-resolution retains the supplied free presentation. -/
@[simp, stacks 0BZ7 "presentation of the canonical self-resolution"]
theorem self_presentation {B : CochainDGAlgebra.{u, v} R}
    (P : Presentation.{u, v, w} B) (hB : B.IsKFlat) :
    (self P hB).presentation = P := sorry

/-- Lemma 22.38.1 (0BZ7): every cochain differential graded `R`-algebra admits a free K-flat
resolution. -/
@[stacks 0BZ7]
theorem nonempty (B : CochainDGAlgebra.{u, v} R) :
    Nonempty (KFlatResolution.{u, v, v} B) := sorry

end KFlatResolution

section

variable {B : CochainDGAlgebra.{u, v} R} (P : KFlatResolution.{u, v, w} B)

#synth CoeOut (KFlatResolution.{u, v, w} B) (CochainDGAlgebra.{u, v} R)

#synth _root_.QuasiIso P.π.toCochainMap

end

end CochainDGAlgebra.Free
