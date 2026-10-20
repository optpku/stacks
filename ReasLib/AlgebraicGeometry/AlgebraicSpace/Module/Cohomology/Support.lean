module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Complement

/-! # Derived global sections with closed support on algebraic spaces -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `cohomologyWithSupport`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasSheafify (smallEtaleTopology (closedImmersionComplement i)) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf (smallEtaleTopology (closedImmersionComplement i)) AddCommGrpCat.{u})]
    [(etaleRestrictionSheaf (closedImmersionComplementι i) AddCommGrpCat.{u}).Additive]
    [PreservesFiniteLimits
      (etaleRestrictionSheaf (closedImmersionComplementι i) AddCommGrpCat.{u})]
    [PreservesFiniteColimits
      (etaleRestrictionSheaf (closedImmersionComplementι i) AddCommGrpCat.{u})]

/-- Global sections supported on a closed subspace are the kernel of degree-zero
cohomological restriction to its open complement. -/
def globalSectionsWithSupportFunctor :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  kernel (sheafCohomologyRestrict (closedImmersionComplementι i) 0)

/-- Evaluation identifies supported global sections with the kernel of restriction
on the given abelian sheaf. -/
def globalSectionsWithSupportFunctor_objIso
    (G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}) :
    (globalSectionsWithSupportFunctor i).obj G ≅
      kernel ((sheafCohomologyRestrict (closedImmersionComplementι i) 0).app G) :=
  PreservesKernel.iso
    ((evaluation (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}) AddCommGrpCat.{u}).obj G)
    (sheafCohomologyRestrict (closedImmersionComplementι i) 0)

variable [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]

/-- Global sections with closed support form an additive functor. -/
instance globalSectionsWithSupportFunctor_additive :
    (globalSectionsWithSupportFunctor i).Additive := by
  sorry

variable [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]

/-- Cohomology with closed support is the right-derived functor of supported global
sections evaluated on the underlying abelian sheaf of a module. -/
def cohomologyWithSupport (F : X.Modules) (q : ℕ) : AddCommGrpCat.{u} :=
  ((globalSectionsWithSupportFunctor i).rightDerived q).obj
    ((SheafOfModules.toSheaf (structureSheaf X)).obj F)

/-- Supported cohomology is computed by right-derived evaluation of supported global sections. -/
theorem cohomologyWithSupport_eq (F : X.Modules) (q : ℕ) :
    cohomologyWithSupport i F q =
      ((globalSectionsWithSupportFunctor i).rightDerived q).obj
        ((SheafOfModules.toSheaf (structureSheaf X)).obj F) := rfl

/-- Cohomology with closed support in integer degrees, with zero in negative degrees. -/
def cohomologyWithSupportInt (F : X.Modules) (q : ℤ) : AddCommGrpCat.{u} :=
  match q with
  | .ofNat n => cohomologyWithSupport i F n
  | .negSucc _ => (HasZeroObject.zero' AddCommGrpCat.{u}).zero

/-- Integer supported cohomology agrees with ordinary supported cohomology in nonnegative degrees. -/
@[simp] theorem cohomologyWithSupportInt_ofNat (F : X.Modules) (n : ℕ) :
    cohomologyWithSupportInt i F (Int.ofNat n) = cohomologyWithSupport i F n := rfl

end AlgebraicGeometry.AlgebraicSpace
