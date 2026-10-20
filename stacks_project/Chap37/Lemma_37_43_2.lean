/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Normalization
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiFinite f] [IsSeparated f]

/- The canonical map from `X` to the normalization of `S` in `X` is
quasi-compact. -/
#check (inferInstance : QuasiCompact f.toNormalization)

/- The canonical map from `X` to the normalization of `S` in `X` is an
open immersion. -/
#check (inferInstance : IsOpenImmersion f.toNormalization)

/- The canonical map from the normalization of `S` in `X` to `S` is
integral. -/
#check (inferInstance : IsIntegralHom f.fromNormalization)

/- Lemma 37.43.2: a quasi-finite separated morphism of schemes is quasi-affine. -/
@[stacks 02LR] #check
  (AlgebraicGeometry.Scheme.Hom.QuasiFinite.quasiAffine (f := f) : QuasiAffineHom f)

end AlgebraicGeometry.Scheme.Hom
