module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Algebra.Field.ZMod
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.ExtensionByZero

/-!
# Extension by zero of `𝒪_{D(2)}` on `Spec ℤ`

On `Spec ℤ`, the extension by zero of `𝒪_{D(2)}` has a nonzero stalk at the generic point
and a zero stalk at the closed point `(2)`, which is a specialization of the generic point.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.DTwoModule

/-- The affine scheme `Spec ℤ`. -/
abbrev specInt : Scheme :=
  Spec (CommRingCat.of ℤ)

/-- The generic point of `Spec ℤ`. -/
def generic : specInt :=
  genericPoint specInt

/-- The closed point `(2)` of `Spec ℤ`. -/
def two : specInt :=
  (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod 2)))) default

/-- The basic open `D(2) ⊆ Spec ℤ`. -/
def dTwo : specInt.Opens :=
  specInt.basicOpen (2 : Γ(specInt, ⊤))

/-- The sheaf of `𝒪_{Spec ℤ}`-modules obtained by extending `𝒪_{D(2)}` by zero. -/
def moduleSheaf : specInt.toRingedSpace.Modules :=
  (RingedSpace.pulledBackModuleSheafExtensionByZeroFromOpen specInt.toRingedSpace dTwo).obj
    (SheafOfModules.unit _)

/-- The generic point of `Spec ℤ` lies in `D(2)`. -/
theorem generic_mem_dTwo : generic ∈ dTwo := sorry

/-- The closed point `(2)` does not lie in `D(2)`. -/
theorem two_not_mem_dTwo : two ∉ dTwo := sorry

/-- The closed point `(2)` is a specialization of the generic point. -/
theorem specializes : Specializes generic two := sorry

/-- The stalk of `moduleSheaf` at the generic point is nonzero. -/
theorem stalk_generic_not_isZero :
    ¬ IsZero (RingedSpace.stalkModuleCat moduleSheaf generic) := sorry

/-- The stalk of `moduleSheaf` at the closed point `(2)` is zero. -/
theorem stalk_two_isZero :
    IsZero (RingedSpace.stalkModuleCat moduleSheaf two) := sorry

end AlgebraicGeometry.DTwoModule
