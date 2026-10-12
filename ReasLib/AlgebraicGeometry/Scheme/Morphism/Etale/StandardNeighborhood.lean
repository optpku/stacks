/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.StandardEtale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Local

/-!
# Standard étale neighborhoods of scheme morphisms

This file gives the canonical morphisms attached to a standard étale presentation and records
the local immersion descriptions of morphisms that are unramified or étale at a point.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- The canonical morphism from a standard étale affine scheme over an affine open `V` to the
affine line over `V`, obtained by evaluating its polynomial coordinate at `P.X`. -/
noncomputable def StandardEtalePair.toAffineLine
    (V : S.affineOpens) (P : StandardEtalePair Γ(S, (V : S.Opens))) :
    Spec (CommRingCat.of P.Ring) ⟶
      Spec (CommRingCat.of (Polynomial Γ(S, (V : S.Opens)))) :=
  Spec.map (CommRingCat.ofHom (Polynomial.aeval P.X).toRingHom)

/-- The structure morphism from a standard étale affine scheme to the affine open over which its
presentation is defined. -/
noncomputable def StandardEtalePair.toAffineOpen
    (V : S.affineOpens) (P : StandardEtalePair Γ(S, (V : S.Opens))) :
    Spec (CommRingCat.of P.Ring) ⟶ (V : S.Opens).toScheme :=
  P.toAffineLine V ≫
    Spec.map (CommRingCat.ofHom Polynomial.C) ≫ V.2.isoSpec.inv

namespace Scheme.Hom.UnramifiedAt

/-- An unramified morphism at a point admits, over any fixed affine target neighborhood, an
affine source neighborhood immersed into a standard étale presentation whose localization
polynomial is the derivative of its monic defining polynomial. -/
theorem exists_affineOpen_immersion_standardEtale
    (x : X) (V : S.affineOpens) (hxV : f x ∈ (V : S.Opens)) (hx : f.UnramifiedAt x) :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
      ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens),
        ∃ P : StandardEtalePair Γ(S, (V : S.Opens)),
          P.g = P.f.derivative ∧
            ∃ j : (U : X.Opens).toScheme ⟶ Spec (CommRingCat.of P.Ring),
              IsImmersion j ∧
                j ≫ P.toAffineOpen V = f.resLE (V : S.Opens) (U : X.Opens) e := sorry

end Scheme.Hom.UnramifiedAt

namespace Scheme.Hom.EtaleAt

/-- An étale morphism at a point admits, over any fixed affine target neighborhood, an affine
source neighborhood openly immersed into a standard étale presentation whose localization
polynomial is the derivative of its monic defining polynomial. -/
theorem exists_affineOpen_openImmersion_standardEtale
    (x : X) (V : S.affineOpens) (hxV : f x ∈ (V : S.Opens)) (hx : f.EtaleAt x) :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
      ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens),
        ∃ P : StandardEtalePair Γ(S, (V : S.Opens)),
          P.g = P.f.derivative ∧
            ∃ j : (U : X.Opens).toScheme ⟶ Spec (CommRingCat.of P.Ring),
              IsOpenImmersion j ∧
                j ≫ P.toAffineOpen V = f.resLE (V : S.Opens) (U : X.Opens) e := sorry

end Scheme.Hom.EtaleAt

end AlgebraicGeometry
