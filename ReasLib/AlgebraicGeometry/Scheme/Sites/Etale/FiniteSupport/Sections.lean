module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.AbelianSupport
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback

/-!
# Sections with finite support on the small étale site

Sections whose reduced closed support is finite over the base form an additive subgroup.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A section of `F` on the small-étale pullback `X_V` has finite support over
`V` when the reduced induced closed subscheme of its étale section support is
finite over `V`. -/
def HasFiniteSupport (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (V : Y.Etale) (σ : F.obj.obj (op ((smallEtalePullback f).obj V))) : Prop :=
  IsFinite
    ((Scheme.ClosedSubschemeStructure.reduced
        (abelianSheafSectionSupport F ((smallEtalePullback f).obj V) σ)).ι ≫
      pullback.fst V.hom f)

/-- Finite support of a section is finiteness of its reduced étale section
support over the base. -/
theorem hasFiniteSupport_iff (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (V : Y.Etale) (σ : F.obj.obj (op ((smallEtalePullback f).obj V))) :
    HasFiniteSupport f F V σ ↔
      IsFinite
        ((Scheme.ClosedSubschemeStructure.reduced
            (abelianSheafSectionSupport F ((smallEtalePullback f).obj V) σ)).ι ≫
          pullback.fst V.hom f) :=
  Iff.rfl

/-- The additive subgroup of sections of `F` on `X_V` whose support is finite
over `V`. -/
def finiteSupportSections (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (V : Y.Etale) :
    AddSubgroup (F.obj.obj (op ((smallEtalePullback f).obj V))) where
  carrier := {σ | HasFiniteSupport f F V σ}
  zero_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry

/-- Membership in the finite-support subgroup is the finite-support
predicate. -/
theorem mem_finiteSupportSections_iff
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : F.obj.obj (op ((smallEtalePullback f).obj V))) :
    σ ∈ finiteSupportSections f F V ↔ HasFiniteSupport f F V σ :=
  Iff.rfl


end AlgebraicGeometry.Scheme.Etale

end
