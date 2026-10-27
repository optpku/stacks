/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Free.Presentation
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.QuasiIso.Basic
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Ulift
public import ReasLib.Algebra.Homology.CochainDGAlgebra.KFlat
public import Mathlib.Logic.Small.Basic
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
theorem nonempty [Small.{v} R] (B : CochainDGAlgebra.{u, v} R) :
    Nonempty (KFlatResolution.{u, v, v} B) := sorry

/-- The canonical comparison from a cochain DGA to its carrier-universe lift.

This is the degreewise `ULift.up` map.  It is written directly because
`CochainDGAlgebra.uliftHom` lifts both its source and target; applying it to
`Hom.id B` would therefore have type `Hom (ulift B) (ulift B)`, rather than the
required `Hom B (ulift B)`.
-/
@[stacks 061X "comparison with the carrier-universe lift"]
def uliftComparison (B : CochainDGAlgebra.{u, v} R) :
    CochainDGAlgebra.Hom B (CochainDGAlgebra.ulift.{u, v, u} B) :=
  { map n := (ULift.moduleEquiv.{u, v, u} (R := R) (M := B.X n)).symm.toLinearMap
    comm_d := by
      intro i j h
      sorry
    map_one := by
      sorry
    map_mul := by
      intro n m a b
      sorry }

/-- The degreewise linear equivalence underlying the carrier-universe comparison. -/
@[stacks 061X "degreewise comparison equivalence for the carrier-universe lift"]
def uliftComparisonEquiv (B : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    B.X n ≃ₗ[R] (CochainDGAlgebra.ulift.{u, v, u} B).X n :=
  ULift.moduleEquiv.{u, v, u}.symm

@[simp, stacks 061X "comparison map is the degreewise universe equivalence"]
theorem uliftComparison_map (B : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    (uliftComparison B).map n = (uliftComparisonEquiv B n).toLinearMap := rfl

@[simp, stacks 061X "comparison map evaluates by ULift.up"]
theorem uliftComparison_apply (B : CochainDGAlgebra.{u, v} R) (n : ℤ)
    (x : B.X n) : (uliftComparison B).map n x = ULift.up x := rfl

/-- Every cochain DGA has a free K-flat resolution after lifting its carrier to a common
universe.  The `Small` instance used here is the canonical universe lift of `R : Type u`; no
smallness assumption on the input DGA is exposed by this unrestricted theorem.
-/
@[stacks 0BZ7 "unrestricted free K-flat resolution after a carrier lift"]
theorem nonempty_unrestricted (B : CochainDGAlgebra.{u, v} R) :
    Nonempty (KFlatResolution.{u, max u v, max u v}
      (CochainDGAlgebra.ulift.{u, v, u} B)) := by
  letI : Small.{max u v} R := Small.mk' (Equiv.ulift : ULift.{v} R ≃ R).symm
  exact nonempty (CochainDGAlgebra.ulift.{u, v, u} B)

/-- Lower only the target of the comparison map of an unrestricted resolution.

This is a genuine heterogeneous DGA homomorphism: its source remains in the enlarged carrier
universe, while the target is the original `B`.  The component formula is the actual
`ULift.down` map, rather than a choice of a smaller resolving complex.
-/
@[stacks 061X "lowered comparison from a lifted resolution"]
def lowerComparison {B : CochainDGAlgebra.{u, v} R}
    (P : KFlatResolution.{u, max u v, max u v}
      (CochainDGAlgebra.ulift.{u, v, u} B)) :
    CochainDGAlgebra.Hom P.complex B where
  map n :=
    { toFun := fun x ↦ (P.π.map n x).down
      map_add' := by
        intro x y
        exact congrArg ULift.down (map_add (P.π.map n) x y)
      map_smul' := by
        intro r x
        exact congrArg ULift.down (map_smul (P.π.map n) r x) }
  comm_d := by
    intro i j h
    apply LinearMap.ext
    intro x
    exact congrArg ULift.down (LinearMap.congr_fun (P.π.comm_d i j h) x)
  map_one := congrArg ULift.down P.π.map_one
  map_mul := by
    intro n m a b
    exact congrArg ULift.down (P.π.map_mul n m a b)

@[simp, stacks 061X "component formula for a lowered resolution comparison"]
theorem lowerComparison_apply {B : CochainDGAlgebra.{u, v} R}
    (P : KFlatResolution.{u, max u v, max u v}
      (CochainDGAlgebra.ulift.{u, v, u} B)) (n : ℤ) (x : P.complex.X n) :
    (lowerComparison P).map n x = (P.π.map n x).down := rfl

/-- Put the lowered comparison in a common carrier universe.  This is the form to which the
same-carrier quasi-isomorphism predicate applies; it records the faithful cohomology comparison
without changing the `KFlatResolution` carrier parameter.
-/
@[stacks 061X "common-carrier lift of a lowered resolution comparison"]
def lowerComparisonLift {B : CochainDGAlgebra.{u, v} R}
    (P : KFlatResolution.{u, max u v, max u v}
      (CochainDGAlgebra.ulift.{u, v, u} B)) :
    CochainDGAlgebra.Hom
      (CochainDGAlgebra.ulift.{u, max u v, max u v} P.complex)
      (CochainDGAlgebra.ulift.{u, v, max u v} B) :=
  CochainDGAlgebra.uliftHom (lowerComparison P)

@[stacks 061X "quasi-isomorphism of the common-carrier lowered comparison"]
theorem lowerComparisonLift_quasiIso {B : CochainDGAlgebra.{u, v} R}
    (P : KFlatResolution.{u, max u v, max u v}
      (CochainDGAlgebra.ulift.{u, v, u} B)) :
    CochainDGAlgebra.quasiIso (lowerComparisonLift P) := sorry

end KFlatResolution

section

variable {B : CochainDGAlgebra.{u, v} R} (P : KFlatResolution.{u, v, w} B)

#synth CoeOut (KFlatResolution.{u, v, w} B) (CochainDGAlgebra.{u, v} R)

#synth _root_.QuasiIso P.π.toCochainMap

end

end CochainDGAlgebra.Free
