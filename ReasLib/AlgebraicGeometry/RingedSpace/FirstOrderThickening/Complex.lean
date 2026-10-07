module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal.Quotient
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Hom
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Complexes of first-order thickenings

A complex of first-order thickenings induces a zero composite on ideal modules and a
canonical trivialization of the first thickening. Short exactness is short exactness of
the contravariant ideal-module row.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.Hom (commRingSheafPushforwardMap)
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IsFirstOrderThickening

variable {X X₁ X₂ X₃ : RingedSpace.{u}}
variable {i₁ : X ⟶ X₁} {i₂ : X ⟶ X₂} {i₃ : X ⟶ X₃}
variable [IsFirstOrderThickening i₁] [IsFirstOrderThickening i₂]
variable [IsFirstOrderThickening i₃]

/-- Two composable thickening morphisms form a complex when their ideal-module maps
`ℐ₃ ⟶ ℐ₂ ⟶ ℐ₁` compose to zero. -/
def IsComplex (f : Hom i₁ i₂) (g : Hom i₂ i₃) : Prop :=
  g.idealMap ≫ f.idealMap = 0

/-- A sequence is a complex exactly when its induced ideal-module composite is zero. -/
theorem isComplex_iff (f : Hom i₁ i₂) (g : Hom i₂ i₃) :
    IsComplex f g ↔ g.idealMap ≫ f.idealMap = 0 := sorry

/-- The kernel ideal of the third inclusion lies in the kernel of the structure-sheaf
map of the composite in a complex of first-order thickenings. -/
theorem isComplex_kernel_le (f : Hom i₁ i₂) (g : Hom i₂ i₃) (hC : IsComplex f g) :
    KernelIdeal.subobject (commRingSheafPushforwardMap i₃) ≤
      KernelIdeal.subobject (commRingSheafPushforwardMap (f.hom ≫ g.hom)) := sorry

/-- Transporting the pushforward along the composite by the inverse of the third
inclusion agrees with pushforward along the inverse of the first inclusion. -/
private theorem complex_pushforward_eq (f : Hom i₁ i₂) (g : Hom i₂ i₃) :
    ((TopCat.Presheaf.presheafEquivOfIso CommRingCat.{u} (asIso i₃.hom.base)).inverse.obj
        ((TopCat.Sheaf.pushforward CommRingCat.{u} (f.hom ≫ g.hom).hom.base).obj
          X₁.sheaf).1) =
      (CategoryTheory.inv i₁.hom.base) _* X₁.presheaf := sorry

-- Local declaration justification (metaprogramming implementation): Lean's module system
-- needs this private constructor to remain usable by the exposed trivialization definition.
set_option backward.privateInPublic true in
/-- The map from the pushforward of the base sheaf to the pushforward along the
composite, obtained by descending through the kernel ideal of the third inclusion. -/
private noncomputable def complexQuotientMap (f : Hom i₁ i₂) (g : Hom i₂ i₃)
    (hC : IsComplex f g) :
    (TopCat.Sheaf.pushforward CommRingCat.{u} i₃.hom.base).obj X.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} (f.hom ≫ g.hom).hom.base).obj X₁.sheaf :=
  (KernelIdeal.quotientIso.{u, u, u} (commRingSheafPushforwardMap i₃)
      (KernelIdeal.quotientComparison_isIso.{u, u, u}
        (commRingSheafPushforwardMap i₃))).inv ≫
    IdealSheaf.Quotient.lift.{u, u, u}
      (KernelIdeal.subobject.{u, u, u} (commRingSheafPushforwardMap i₃))
      (commRingSheafPushforwardMap (f.hom ≫ g.hom)) (isComplex_kernel_le f g hC)

-- Local declaration justification (metaprogramming implementation): Lean's module system
-- needs this private constructor to remain usable by the exposed trivialization definition.
set_option backward.privateInPublic true in
/-- The sheaf morphism on the base obtained by transporting the quotient comparison
of a complex along the inverse of the third inclusion. -/
private noncomputable def canonicalTrivializationSheafMap (f : Hom i₁ i₂) (g : Hom i₂ i₃)
    (hC : IsComplex f g) :
    X.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} (CategoryTheory.inv i₁.hom.base)).obj
        X₁.sheaf :=
  { hom :=
      (TopCat.Presheaf.presheafEquivOfIso CommRingCat.{u}
          (asIso i₃.hom.base)).unit.app X.presheaf ≫
        (TopCat.Presheaf.presheafEquivOfIso CommRingCat.{u}
          (asIso i₃.hom.base)).inverse.map (complexQuotientMap f g hC).hom ≫
        eqToHom (complex_pushforward_eq f g) }

-- Local declaration justification (metaprogramming implementation): Lean's public module
-- elaboration needs access to the private sheaf-map constructor in this exposed body.
set_option backward.privateInPublic true in
/-- A complex of first-order thickenings determines a canonical retraction of the
first inclusion by descending its composite through the third inclusion. -/
noncomputable def canonicalTrivialization (f : Hom i₁ i₂) (g : Hom i₂ i₃)
    (hC : IsComplex f g) : X₁ ⟶ X :=
  InducedCategory.homMk
    { base := CategoryTheory.inv i₁.hom.base
      c := (canonicalTrivializationSheafMap f g hC).hom }

/-- The canonical trivialization is a left inverse of the first inclusion. -/
theorem canonicalTrivialization_leftInv (f : Hom i₁ i₂) (g : Hom i₂ i₃)
    (hC : IsComplex f g) :
    i₁ ≫ canonicalTrivialization f g hC = 𝟙 X := sorry

/-- The composite in a complex factors through the canonical trivialization and the
third inclusion. -/
theorem comp_eq_canonicalTrivialization_comp_inclusion (f : Hom i₁ i₂)
    (g : Hom i₂ i₃) (hC : IsComplex f g) :
    f.hom ≫ g.hom = canonicalTrivialization f g hC ≫ i₃ := sorry

/-- The short complex of ideal modules `ℐ₃ ⟶ ℐ₂ ⟶ ℐ₁` induced by a complex of thickenings. -/
noncomputable def idealSheafShortComplex (f : Hom i₁ i₂) (g : Hom i₂ i₃)
    (hC : IsComplex f g) : ShortComplex X.Modules :=
  ShortComplex.mk g.idealMap f.idealMap hC

/-- A sequence of first-order thickenings is short exact when its induced ideal-module
row is a short exact sequence. -/
def IsShortExact (f : Hom i₁ i₂) (g : Hom i₂ i₃) : Prop :=
  ∃ hC : IsComplex f g, (idealSheafShortComplex f g hC).ShortExact

/-- Short exactness is equivalent to the complex condition, exactness at the middle
ideal module, monicity of the first ideal map, and epicity of the second. -/
theorem isShortExact_iff (f : Hom i₁ i₂) (g : Hom i₂ i₃) :
    IsShortExact f g ↔
      ∃ hC : IsComplex f g,
        (idealSheafShortComplex f g hC).Exact ∧
          Mono g.idealMap ∧ Epi f.idealMap := sorry

/-- A short exact sequence of first-order thickenings is a complex. -/
theorem isComplex_of_isShortExact (f : Hom i₁ i₂) (g : Hom i₂ i₃)
    (hSE : IsShortExact f g) : IsComplex f g := sorry

end AlgebraicGeometry.RingedSpace.IsFirstOrderThickening
