/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Catenary
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
public import ReasLib.RingTheory.Catenary.Universally
import Mathlib.Tactic.CrossRefAttribute

/-!
# Locality of universal catenarity

Open-cover and affine-coordinate-ring criteria for universal catenarity of locally Noetherian
schemes.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable (S : Scheme.{u}) [IsLocallyNoetherian S]

/-- A locally Noetherian scheme is universally catenary exactly when it admits an open cover
by universally catenary open subschemes. -/
theorem universallyCatenary_iff_exists_openCover :
    UniversallyCatenary S ↔
      ∃ 𝒰 : S.OpenCover, ∀ i : 𝒰.I₀, UniversallyCatenary (𝒰.X i) := sorry

/-- A locally Noetherian scheme is universally catenary exactly when every affine open has a
universally catenary section ring. -/
theorem UniversallyCatenary.iff_forall_affineOpen :
    UniversallyCatenary S ↔
      ∀ U : S.affineOpens, UniversallyCatenaryRing.{u, u} (Γ(S, U)) := sorry

/-- A locally Noetherian scheme is universally catenary exactly when it admits an affine open
cover whose section rings are universally catenary. -/
theorem UniversallyCatenary.iff_exists_affineOpenCover :
    UniversallyCatenary S ↔
      ∃ 𝒰 : S.AffineOpenCover,
        ∀ i : 𝒰.I₀, UniversallyCatenaryRing.{u, u} (Γ(S, (𝒰.f i).opensRange)) := sorry

/-- Universal catenarity, universal catenarity on an open cover, universal catenarity of every
affine-open section ring, and universal catenarity of the section rings on one affine open cover
are equivalent for a locally Noetherian scheme. -/
@[stacks 02J9]
theorem universallyCatenary_tfae :
    List.TFAE
      [ UniversallyCatenary S,
        ∃ 𝒰 : S.OpenCover, ∀ i : 𝒰.I₀, UniversallyCatenary (𝒰.X i),
        ∀ U : S.affineOpens, UniversallyCatenaryRing.{u, u} (Γ(S, U)),
        ∃ 𝒰 : S.AffineOpenCover,
          ∀ i : 𝒰.I₀,
            UniversallyCatenaryRing.{u, u} (Γ(S, (𝒰.f i).opensRange)) ] := sorry

end AlgebraicGeometry
