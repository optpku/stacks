/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedAffineSpace
import Mathlib.Tactic.CrossRefAttribute

/-!
# The punctured affine plane
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

noncomputable section

universe u

namespace PuncturedAffinePlane

section CommRing

variable (k : Type u) [CommRing k]

/-- The coordinate ring `k[x,y]` of the affine plane. -/
@[stacks 01IL "punctured affine-plane coordinate ring"]
abbrev coordinateRing : Type u :=
  PuncturedAffineSpace.coordinateRing (ULift.{u} (Fin 2)) k

/-- The affine plane over `k`, using mathlib's relative affine-space owner. -/
@[stacks 01IL "punctured affine-plane affine-space model"]
abbrev affinePlane : Scheme.{u} :=
  PuncturedAffineSpace.affineSpace (ULift.{u} (Fin 2)) k

/-- The canonical structure morphism from affine `2`-space to `Spec(k)`. -/
@[stacks 01IL "punctured affine-plane structure morphism"]
abbrev toBase : affinePlane k ⟶ Spec (CommRingCat.of k) :=
  PuncturedAffineSpace.toBase (ULift.{u} (Fin 2)) k

/-- The polynomial coordinate `x`. -/
@[stacks 01IL "punctured affine-plane x coordinate"]
abbrev x : coordinateRing k :=
  PuncturedAffineSpace.coordinate (ULift.{u} (Fin 2)) k (ULift.up 0)

/-- The polynomial coordinate `y`. -/
@[stacks 01IL "punctured affine-plane y coordinate"]
abbrev y : coordinateRing k :=
  PuncturedAffineSpace.coordinate (ULift.{u} (Fin 2)) k (ULift.up 1)

/-- The global coordinate section `x`. -/
@[stacks 01IL "punctured affine-plane x section"]
abbrev xSection : Γ(affinePlane k, ⊤) :=
  PuncturedAffineSpace.coordinateSection (ULift.{u} (Fin 2)) k (ULift.up 0)

/-- The global coordinate section `y`. -/
@[stacks 01IL "punctured affine-plane y section"]
abbrev ySection : Γ(affinePlane k, ⊤) :=
  PuncturedAffineSpace.coordinateSection (ULift.{u} (Fin 2)) k (ULift.up 1)

/-- Evaluation at the affine-plane origin as a `k`-algebra homomorphism. -/
@[stacks 01IL "punctured affine-plane origin algebra map"]
abbrev evalAtOriginAlgHom : coordinateRing k →ₐ[k] k :=
  PuncturedAffineSpace.evalAtOriginAlgHom (ULift.{u} (Fin 2)) k

/-- The ring-hom view of evaluation at the affine-plane origin. -/
@[stacks 01IL "punctured affine-plane origin evaluation"]
abbrev evalAtOrigin : coordinateRing k →+* k :=
  (evalAtOriginAlgHom k).toRingHom

/-- The ideal of functions vanishing along the zero section. -/
@[stacks 01IL "punctured affine-plane origin ideal"]
abbrev originIdeal : Ideal (coordinateRing k) :=
  PuncturedAffineSpace.originIdeal (ULift.{u} (Fin 2)) k

/-- The kernel description of the origin is the ideal `(x,y)`. -/
@[stacks 01IL "punctured affine-plane origin ideal generators"]
theorem originIdeal_eq_span :
    originIdeal k = Ideal.span ({x k, y k} : Set (coordinateRing k)) := sorry

/-- The basic open `D(x)` in the affine plane. -/
@[stacks 01IL "punctured affine-plane X chart"]
abbrev chartX : (affinePlane k).Opens :=
  (affinePlane k).basicOpen (xSection k)

/-- The basic open `D(y)` in the affine plane. -/
@[stacks 01IL "punctured affine-plane Y chart"]
abbrev chartY : (affinePlane k).Opens :=
  (affinePlane k).basicOpen (ySection k)

/-- The basic open `D(xy)`. -/
@[stacks 01IL "punctured affine-plane overlap chart"]
abbrev chartXY : (affinePlane k).Opens :=
  (affinePlane k).basicOpen (xSection k * ySection k)

/-- The punctured affine plane, represented by `D(x) ∪ D(y)`. -/
@[stacks 01IL "punctured affine plane"]
abbrev puncturedOpen : (affinePlane k).Opens :=
  PuncturedAffineSpace.puncturedOpen (ULift.{u} (Fin 2)) k

/-- The punctured affine plane is covered by `D(x)` and `D(y)`. -/
@[stacks 01IL "standard cover of the punctured affine plane"]
theorem puncturedOpen_eq_chartX_sup_chartY :
    puncturedOpen k = chartX k ⊔ chartY k := sorry

/-- The basic open `D(x)` is affine. -/
@[stacks 01IL "first affine chart of the punctured affine plane"]
theorem chartX_isAffineOpen : IsAffineOpen (chartX k) := sorry

/-- The basic open `D(y)` is affine. -/
@[stacks 01IL "second affine chart of the punctured affine plane"]
theorem chartY_isAffineOpen : IsAffineOpen (chartY k) := sorry

/-- The intersection `D(x) ∩ D(y)` is `D(xy)`. -/
@[stacks 01IL "intersection of the standard affine charts"]
theorem chartX_inf_chartY : chartX k ⊓ chartY k = chartXY k := sorry

/-- The basic open `D(xy)` is affine. -/
@[stacks 01IL "affine overlap of the standard charts"]
theorem chartXY_isAffineOpen : IsAffineOpen (chartXY k) := sorry

/-- The canonical map from `k[x,y]` to global sections of the punctured affine plane. -/
@[stacks 01IL "punctured-affine-plane global-sections comparison"]
noncomputable abbrev globalSectionsComparison :
    CommRingCat.of (coordinateRing k) ⟶
      Scheme.Γ.obj (Opposite.op (puncturedOpen k).toScheme) :=
  PuncturedAffineSpace.globalSectionsComparison (ULift.{u} (Fin 2)) k

namespace globalSectionsComparison

/-- The two-coordinate specialization of the punctured-affine global-sections comparison is an
isomorphism. -/
@[stacks 01IL "punctured affine-plane global sections"]
theorem isIso : IsIso (globalSectionsComparison k) := sorry

end globalSectionsComparison

end CommRing

section Field

variable (k : Type u) [Field k]

/-- The origin point of the canonical affine plane. -/
@[stacks 01IL "origin"]
noncomputable abbrev origin : affinePlane k :=
  PuncturedAffineSpace.origin (ULift.{u} (Fin 2)) k

namespace puncturedOpen

/-- The punctured affine plane is the complement of its origin. -/
@[stacks 01IL "punctured affine plane as the complement of the origin"]
theorem coe_eq_compl_origin :
    (puncturedOpen k : Set (affinePlane k)) =
      ({origin k} : Set (affinePlane k))ᶜ := sorry

end puncturedOpen

/-- The punctured affine plane over a field is not affine. -/
@[stacks 01IL "nonaffineness"]
theorem not_isAffine : ¬ IsAffine (puncturedOpen k).toScheme := sorry

end Field
end PuncturedAffinePlane
end
end AlgebraicGeometry
