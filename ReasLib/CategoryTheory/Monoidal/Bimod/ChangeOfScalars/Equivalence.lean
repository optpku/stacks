module

public import ReasLib.CategoryTheory.Functor.Equivalence
public import ReasLib.CategoryTheory.Monoidal.Bimod.ChangeOfScalars
import Mathlib.Tactic.CrossRefAttribute

/-!
# Restriction of module objects along an isomorphism

Restriction of scalars along a monoid isomorphism is an equivalence of module categories.  Both
directions keep the ambient carrier unchanged.  This is the canonical normalization tool when two
presentations of the same coefficient monoid are isomorphic but not definitionally equal.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace CategoryTheory.Bimod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {A B : Mon C}

/-- Restriction along the inverse of a monoid isomorphism, viewed as transport of right modules
in the forward direction. -/
@[stacks 0FSA "right module transport along a monoid isomorphism"]
def restrictRightIso (e : A ≅ B) : RightModule A ⥤ RightModule B :=
  restrictRight (Mon.trivial C) e.inv

/-- Restriction along the forward map of a monoid isomorphism, inverse to
`restrictRightIso e`. -/
@[stacks 0FSA "inverse right module transport along a monoid isomorphism"]
def restrictRightIsoInverse (e : A ≅ B) : RightModule B ⥤ RightModule A :=
  restrictRight (Mon.trivial C) e.hom

/-- The objectwise unit comparison for transport of right modules along a monoid isomorphism. -/
noncomputable def restrictRightIsoUnitApp (e : A ≅ B) (M : RightModule A) :
    M ≅ ((restrictRightIso e ⋙ restrictRightIsoInverse e).obj M) :=
  Bimod.isoOfIso (Iso.refl M.X) sorry sorry

/-- The objectwise counit comparison for transport of right modules along a monoid isomorphism. -/
noncomputable def restrictRightIsoCounitApp (e : A ≅ B) (M : RightModule B) :
    ((restrictRightIsoInverse e ⋙ restrictRightIso e).obj M) ≅ M :=
  Bimod.isoOfIso (Iso.refl M.X) sorry sorry

/-- The natural unit comparison for transport of right modules along a monoid isomorphism. -/
noncomputable def restrictRightIsoUnit (e : A ≅ B) :
    𝟭 (RightModule A) ≅ restrictRightIso e ⋙ restrictRightIsoInverse e :=
  NatIso.ofComponents (restrictRightIsoUnitApp e) (fun _ ↦ sorry)

/-- The natural counit comparison for transport of right modules along a monoid isomorphism. -/
noncomputable def restrictRightIsoCounit (e : A ≅ B) :
    restrictRightIsoInverse e ⋙ restrictRightIso e ≅ 𝟭 (RightModule B) :=
  NatIso.ofComponents (restrictRightIsoCounitApp e) (fun _ ↦ sorry)

/-- Explicit quasi-inverse data for restriction of right modules along a monoid isomorphism. -/
@[stacks 0FSA "right module restriction quasi-inverse"]
noncomputable def restrictRightIsoQuasiInverse (e : A ≅ B) :
    Functor.QuasiInverse (restrictRightIso e) where
  inverse := restrictRightIsoInverse e
  unitIso := restrictRightIsoUnit e
  counitIso := restrictRightIsoCounit e

/-- Restriction of right modules along a monoid isomorphism is an equivalence which preserves
the underlying carrier in both directions. -/
@[stacks 0FSA "right module equivalence along a monoid isomorphism"]
noncomputable def restrictRightEquivalence (e : A ≅ B) : RightModule A ≌ RightModule B :=
  (restrictRightIsoQuasiInverse e).adjointifyUnit

/-- The forward functor of `restrictRightEquivalence e` is carrier-preserving restriction along
`e.inv`. -/
@[simp]
theorem restrictRightEquivalence_functor (e : A ≅ B) :
    (restrictRightEquivalence e).functor = restrictRightIso e := sorry

/-- The inverse functor of `restrictRightEquivalence e` is carrier-preserving restriction along
`e.hom`. -/
@[simp]
theorem restrictRightEquivalence_inverse (e : A ≅ B) :
    (restrictRightEquivalence e).inverse = restrictRightIsoInverse e := sorry

end CategoryTheory.Bimod

end
