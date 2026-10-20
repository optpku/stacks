/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Curve.PurelyInseparable.Genus
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom
open Scheme.Hom.IsNonconstant

universe u

/- Lemma 53.13.5 (1): for a nonconstant morphism of proper nonsingular curves over a
field of characteristic `p > 0`, with smooth source, constant global functions on `X`, and
purely inseparable induced function-field extension, the target is smooth. -/
@[stacks 0CD0] #check (AlgebraicGeometry.Curve.smooth_of_isPurelyInseparable :
    ∀ {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (X Y : SchemeOverField k) [Curve X] [Curve Y]
    [Scheme.Regular X.left] [Scheme.Regular Y.left]
    [IsProper X.hom] [IsProper Y.hom] [Smooth X.hom]
    (f : X ⟶ Y) (hf : f.left.IsNonconstant)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_pi : (f.left.functionFieldMap
      ((AlgebraicGeometry.isDominant_iff_map_genericPoint_eq f.left).mp
        (isDominant_of_curves hf))).IsPurelyInseparable),
    Smooth Y.hom)

/- Lemma 53.13.5 (2): under the same hypotheses, the canonical map from `k` to the
global functions on `Y` is bijective. -/
@[stacks 0CD0] #check (AlgebraicGeometry.Curve.globalSectionsMap_bijective_of_isPurelyInseparable :
    ∀ {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (X Y : SchemeOverField k) [Curve X] [Curve Y]
    [Scheme.Regular X.left] [Scheme.Regular Y.left]
    [IsProper X.hom] [IsProper Y.hom] [Smooth X.hom]
    (f : X ⟶ Y) (hf : f.left.IsNonconstant)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_pi : (f.left.functionFieldMap
      ((AlgebraicGeometry.isDominant_iff_map_genericPoint_eq f.left).mp
        (isDominant_of_curves hf))).IsPurelyInseparable),
    Function.Bijective (Scheme.Hom.globalSectionsMap Y.hom))

/- Lemma 53.13.5 (3): under the same hypotheses, the genus of `Y` equals the genus of `X`,
using the canonical dimension-one and global-sections proofs. -/
@[stacks 0CD0] #check (AlgebraicGeometry.Curve.genus_eq_of_isPurelyInseparable :
    ∀ {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (X Y : SchemeOverField k) [Curve X] [Curve Y]
    [Scheme.Regular X.left] [Scheme.Regular Y.left]
    [IsProper X.hom] [IsProper Y.hom] [Smooth X.hom]
    (f : X ⟶ Y) (hf : f.left.IsNonconstant)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_pi : (f.left.functionFieldMap
      ((AlgebraicGeometry.isDominant_iff_map_genericPoint_eq f.left).mp
        (isDominant_of_curves hf))).IsPurelyInseparable),
    SchemeOverField.genus Y (AlgebraicGeometry.topologicalKrullDim_eq_one Y)
        (AlgebraicGeometry.Curve.globalSectionsMap_bijective_of_isPurelyInseparable
          p X Y f hf hΓ h_pi) =
      SchemeOverField.genus X (AlgebraicGeometry.topologicalKrullDim_eq_one X) hΓ)
