module

public import ReasLib.CategoryTheory.Monoidal.Picard
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal

/-!
# Picard groups of algebraic spaces

The Picard group of an algebraic space is the group of isomorphism classes of
tensor-invertible modules on the small étale ringed site. This is the
algebraic-space specialization of `MonoidalCategory.PicardGroup`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The Picard group of an algebraic space, formed from tensor-invertible sheaves
of modules on the small étale site. -/
abbrev PicardGroup (X : AlgebraicSpace S) :=
  MonoidalCategory.PicardGroup X.Modules

namespace Modules

/-- The Picard class represented by an invertible sheaf of modules on an
algebraic space. -/
abbrev picardClass {X : AlgebraicSpace S}
    (L : X.Modules) [isInvertibleObject L] : X.PicardGroup :=
  MonoidalCategory.PicardGroup.mk L

end Modules

namespace PicardGroup

/-- The chosen invertible module representative of a Picard class. -/
abbrev repr {X : AlgebraicSpace S} (x : X.PicardGroup) : X.Modules :=
  MonoidalCategory.PicardGroup.repr x

end PicardGroup

/-- Two invertible modules represent the same Picard class exactly when they are
isomorphic. -/
theorem picardClass_eq_iff {X : AlgebraicSpace S}
    (L N : X.Modules) [isInvertibleObject L] [isInvertibleObject N] :
    Modules.picardClass L = Modules.picardClass N ↔ Nonempty (L ≅ N) := sorry

end AlgebraicGeometry.AlgebraicSpace
