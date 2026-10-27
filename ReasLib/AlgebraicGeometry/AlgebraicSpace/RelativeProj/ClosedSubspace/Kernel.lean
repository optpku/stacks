/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Subobject.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists.Psi
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Triple

/-!
# Degreewise kernels of closed subspaces of relative Proj

A closed subspace `i : Z ⟶ underline{Proj}_X(𝒜)` determines the canonical
degree-`d` map `𝒜_d ⟶ π_* ((i_* 𝒪_Z)(d))`, obtained from `CanonicalTwists.psi`
by adjunction, restriction along `i`, and pushforward composition. Its kernel
is the homogeneous piece of the ideal cutting out `Z`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
variable {deg : DegreePieces 𝒜} (F : ProjFunctor X 𝒜)
variable (hF : F.IsAssociatedToQuadruples deg)
variable {Z : AlgebraicSpace S} (i : Z ⟶ toAlgebraicSpace F hF)

/-- The pullback `i^* 𝒪_P(d)` of a canonical Serre twist along a closed subspace. -/
def closedSubspaceTwist (d : ℤ) : Z.Modules :=
  (Modules.pullback i).obj (CanonicalTwists.obj F hF d)

/-- `closedSubspaceTwist` is pullback of `CanonicalTwists.obj`. -/
theorem closedSubspaceTwist_eq (d : ℤ) :
    closedSubspaceTwist F hF i d =
      (Modules.pullback i).obj (CanonicalTwists.obj F hF d) :=
  sorry

/-- The pushforward `π_* ((i_* 𝒪_Z)(d))`, encoded as `(i ≫ π)_* i^* 𝒪_P(d)`. -/
def closedSubspaceDegreePiece (d : ℕ) : X.Modules :=
  (Modules.pushforward (i ≫ toAlgebraicSpace_hom F hF)).obj
    (closedSubspaceTwist F hF i (Int.ofNat d))

/-- `closedSubspaceDegreePiece` is pushforward of `closedSubspaceTwist` along `i ≫ π`. -/
theorem closedSubspaceDegreePiece_eq (d : ℕ) :
    closedSubspaceDegreePiece F hF i d =
      (Modules.pushforward (i ≫ toAlgebraicSpace_hom F hF)).obj
        (closedSubspaceTwist F hF i (Int.ofNat d)) :=
  sorry

/-- The canonical degree-`d` map `𝒜_d ⟶ π_* ((i_* 𝒪_Z)(d))`, obtained as the adjoint of
`CanonicalTwists.psi`, followed by `π_*` of the adjunction unit of `i`, followed by the
pushforward-composition comparison. -/
def closedSubspaceDegreeMap [IsClosedImmersion i] (d : ℕ) :
    deg.obj d ⟶ closedSubspaceDegreePiece F hF i d :=
  ((Modules.pullbackPushforwardAdjunction (toAlgebraicSpace_hom F hF)).homEquiv
      (deg.obj d) (CanonicalTwists.obj F hF (Int.ofNat d)))
      ((CanonicalTwists.psi F hF).hom d) ≫
    (Modules.pushforward (toAlgebraicSpace_hom F hF)).map
      ((Modules.pullbackPushforwardAdjunction i).unit.app
        (CanonicalTwists.obj F hF (Int.ofNat d))) ≫
    (Modules.pushforwardComp i (toAlgebraicSpace_hom F hF)).hom.app
      (closedSubspaceTwist F hF i (Int.ofNat d))

/-- `closedSubspaceDegreeMap` is the three-leg composite of the adjoint of `psi`,
restriction along `i`, and `pushforwardComp`. -/
theorem closedSubspaceDegreeMap_eq [IsClosedImmersion i] (d : ℕ) :
    closedSubspaceDegreeMap F hF i d =
      ((Modules.pullbackPushforwardAdjunction (toAlgebraicSpace_hom F hF)).homEquiv
          (deg.obj d) (CanonicalTwists.obj F hF (Int.ofNat d)))
          ((CanonicalTwists.psi F hF).hom d) ≫
        (Modules.pushforward (toAlgebraicSpace_hom F hF)).map
          ((Modules.pullbackPushforwardAdjunction i).unit.app
            (CanonicalTwists.obj F hF (Int.ofNat d))) ≫
        (Modules.pushforwardComp i (toAlgebraicSpace_hom F hF)).hom.app
          (closedSubspaceTwist F hF i (Int.ofNat d)) :=
  sorry

/-- The homogeneous piece `I_d ⊂ 𝒜_d` of the kernel of the canonical map to
`π_* ((i_* 𝒪_Z)(d))`. -/
def closedSubspaceDegreeKernel [IsClosedImmersion i] (d : ℕ) :
    Subobject (deg.obj d) :=
  kernelSubobject (closedSubspaceDegreeMap F hF i d)

/-- `closedSubspaceDegreeKernel` is the kernel subobject of `closedSubspaceDegreeMap`. -/
theorem closedSubspaceDegreeKernel_eq [IsClosedImmersion i] (d : ℕ) :
    closedSubspaceDegreeKernel F hF i d =
      kernelSubobject (closedSubspaceDegreeMap F hF i d) :=
  sorry

/-- The inclusion of the degree-`d` kernel is annihilated by the canonical degree map. -/
theorem closedSubspaceDegreeKernel_arrow_comp [IsClosedImmersion i] (d : ℕ) :
    (closedSubspaceDegreeKernel F hF i d).arrow ≫
      closedSubspaceDegreeMap F hF i d = 0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
