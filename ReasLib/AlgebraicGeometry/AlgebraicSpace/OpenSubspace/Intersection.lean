/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.BaseChange

/-!
# Intersections of open subspaces of algebraic spaces

The intersection of two open subspaces is their fibre product, viewed as an
open subspace of the second one.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The intersection of two open subspaces, viewed as an open subspace of the
second, is the pullback of their inclusions. -/
def OpenSubspace.preimage {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U V : OpenSubspace X) : OpenSubspace V.X where
  X := pullback U.ι V.ι
  ι := pullback.snd U.ι V.ι
  isOpenImmersion := IsOpenImmersion.pullback_snd U.isOpenImmersion V.ι

/-- The underlying space of the intersection is the fibre product of the inclusions. -/
theorem OpenSubspace.preimage_X {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U V : OpenSubspace X) : (U.preimage V).X = pullback U.ι V.ι :=
  rfl

/-- The inclusion of the intersection is the second fibre-product projection. -/
theorem OpenSubspace.preimage_ι {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U V : OpenSubspace X) : (U.preimage V).ι = pullback.snd U.ι V.ι :=
  rfl

/-- The intersection is the fibre product, included into the second open subspace
by its second projection, which is an open immersion. -/
theorem OpenSubspace.preimage_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U V : OpenSubspace X) :
    (U.preimage V).X = pullback U.ι V.ι ∧
      (U.preimage V).ι = pullback.snd U.ι V.ι ∧
        IsOpenImmersion (U.preimage V).ι :=
  ⟨rfl, rfl, (U.preimage V).isOpenImmersion⟩

end AlgebraicGeometry.AlgebraicSpace
