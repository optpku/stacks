module

public import ReasLib.AlgebraicGeometry.Scheme.K0.Support

/-!
# Universal support comparison for perfect `K₀`

Every perfect complex is supported on `Set.univ`, so forgetting support is an
additive equivalence `K0WithSupport X Set.univ ≃+ K0 X`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

/-- Every derived module is cohomologically supported on `Set.univ`. -/
theorem isSupportedOn_univ {X : RingedSpace.{u}} (K : ModuleDerived X) :
    IsSupportedOn K Set.univ := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived

namespace AlgebraicGeometry.Scheme.K0WithSupport

/-- A perfect derived module, viewed as supported on `Set.univ`. -/
def restrictObj (X : Scheme.{u})
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :
    RingedSpace.ModuleDerived.PerfectSupportedOn (Set.univ : Set X) :=
  ⟨K.obj, ⟨K.property, RingedSpace.ModuleDerived.isSupportedOn_univ K.obj⟩⟩

/-- The underlying derived object of `restrictObj` is the original perfect complex. -/
theorem restrictObj_obj (X : Scheme.{u})
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :
    (restrictObj X K).obj = K.obj := sorry

/-- Triangle relations in perfect `K₀` are killed by the universal-support inclusion. -/
theorem relations_le_ker_restrict (X : Scheme.{u}) :
    TriangulatedK0.relations
        (RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) ≤
      (FreeAbelianGroup.lift fun K :
          RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace) ↦
        TriangulatedK0.of (restrictObj X K)).ker := sorry

/-- The inclusion of perfect `K₀` into universal-support `K₀`. -/
def restrict (X : Scheme.{u}) : K0 X →+ K0WithSupport X Set.univ :=
  TriangulatedK0.lift (fun K ↦ TriangulatedK0.of (restrictObj X K))
    (relations_le_ker_restrict X)

/-- The universal-support inclusion sends a perfect generator to its supported class. -/
theorem restrict_of (X : Scheme.{u})
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :
    restrict X (TriangulatedK0.of K) = TriangulatedK0.of (restrictObj X K) := sorry

/-- Forgetting support is inverse to the universal-support inclusion on the left. -/
theorem restrict_forget (X : Scheme.{u}) (a : K0WithSupport X Set.univ) :
    restrict X (forget X Set.univ a) = a := sorry

/-- Forgetting support is inverse to the universal-support inclusion on the right. -/
theorem forget_restrict (X : Scheme.{u}) (a : K0 X) :
    forget X Set.univ (restrict X a) = a := sorry

/-- Identifying supported-perfect `K₀` on `Z = X` with ordinary perfect `K₀`. -/
def equivK0 (X : Scheme.{u}) : K0WithSupport X Set.univ ≃+ K0 X where
  toFun := forget X Set.univ
  invFun := restrict X
  left_inv := restrict_forget X
  right_inv := forget_restrict X
  map_add' := (forget X Set.univ).map_add

/-- The forward map of `equivK0` is the support-forgetting homomorphism. -/
theorem equivK0_apply (X : Scheme.{u}) (a : K0WithSupport X Set.univ) :
    equivK0 X a = forget X Set.univ a := sorry

/-- The inverse map of `equivK0` is the universal-support inclusion. -/
theorem equivK0_symm_apply (X : Scheme.{u}) (a : K0 X) :
    (equivK0 X).symm a = restrict X a := sorry

/-- Forgetting the support condition is bijective when the support is `Set.univ`. -/
theorem forget_bijective_univ (X : Scheme.{u}) :
    Function.Bijective (forget X Set.univ) := sorry

end AlgebraicGeometry.Scheme.K0WithSupport
