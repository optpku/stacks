/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.RelativeNormalization
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : Y ⟶ X)
variable [QuasiCompact f] [QuasiSeparated f] [IsDominant f]

/- Definition 29.55.6

For a quasi-compact, quasi-separated, dominant morphism `f : Y ⟶ X`, a relative
seminormalization is the initial factorization constructed in Lemma 29.55.5 (2), and a relative
weak normalization is the initial factorization constructed in Lemma 29.55.5 (1).
-/
@[stacks 0H3P] #check
  (AlgebraicGeometry.Scheme.Hom.RelativeSeminormalization f : Type (u + 1))

#check (AlgebraicGeometry.Scheme.Hom.RelativeSeminormalization.toFactorisation :
  RelativeSeminormalization f → CategoryTheory.Factorisation f)

#check (AlgebraicGeometry.Scheme.Hom.RelativeSeminormalization.obj :
  RelativeSeminormalization f → Scheme.{u})

#check (AlgebraicGeometry.Scheme.Hom.RelativeSeminormalization.fromSource :
  ∀ S : RelativeSeminormalization f, Y ⟶ S.obj)

#check (AlgebraicGeometry.Scheme.Hom.RelativeSeminormalization.toTarget :
  ∀ S : RelativeSeminormalization f, S.obj ⟶ X)

#check (AlgebraicGeometry.Scheme.Hom.RelativeSeminormalization.fromSource_comp_toTarget :
  ∀ S : RelativeSeminormalization f, S.fromSource ≫ S.toTarget = f)

#check (AlgebraicGeometry.Scheme.Hom.RelativeSeminormalization.toTarget_property :
  ∀ S : RelativeSeminormalization f,
    UniversalHomeomorphism S.toTarget ∧
      ∀ x : S.obj, IsIso (Scheme.Hom.residueFieldMap S.toTarget x))

#check (AlgebraicGeometry.Scheme.Hom.RelativeSeminormalization.nonempty_isInitial :
  ∀ S : RelativeSeminormalization f, Nonempty (IsInitial S.1))

#check (AlgebraicGeometry.Scheme.Hom.RelativeWeakNormalization f : Type (u + 1))

#check (AlgebraicGeometry.Scheme.Hom.RelativeWeakNormalization.toFactorisation :
  RelativeWeakNormalization f → CategoryTheory.Factorisation f)

#check (AlgebraicGeometry.Scheme.Hom.RelativeWeakNormalization.obj :
  RelativeWeakNormalization f → Scheme.{u})

#check (AlgebraicGeometry.Scheme.Hom.RelativeWeakNormalization.fromSource :
  ∀ W : RelativeWeakNormalization f, Y ⟶ W.obj)

#check (AlgebraicGeometry.Scheme.Hom.RelativeWeakNormalization.toTarget :
  ∀ W : RelativeWeakNormalization f, W.obj ⟶ X)

#check (AlgebraicGeometry.Scheme.Hom.RelativeWeakNormalization.fromSource_comp_toTarget :
  ∀ W : RelativeWeakNormalization f, W.fromSource ≫ W.toTarget = f)

#check (AlgebraicGeometry.Scheme.Hom.RelativeWeakNormalization.isUniversalHomeomorphism_toTarget :
  ∀ W : RelativeWeakNormalization f, UniversalHomeomorphism W.toTarget)

#check (AlgebraicGeometry.Scheme.Hom.RelativeWeakNormalization.nonempty_isInitial :
  ∀ W : RelativeWeakNormalization f, Nonempty (IsInitial W.1))

end Scheme.Hom
end AlgebraicGeometry
