/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Homology
public import ReasLib.CategoryTheory.ObjectProperty.Orthogonal.Retract

/-!
# K-injective differential graded module sheaves

K-injectivity is expressed intrinsically in the DG homotopy category: a target is
K-injective when it is right orthogonal to all acyclic DG modules.  This avoids replacing a DG
module by a cochain complex in an additional homological direction.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

-- Mathlib intentionally keeps this construction non-global because a global instance breaks
-- sheaf/free elaboration.  Orthogonality is formed in the pinned homotopy triangulation.
attribute [local instance] Abelian.hasFiniteBiproducts

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule.Homotopy

section


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- The K-injective objects in the intrinsic DG homotopy category are the right orthogonal of
the acyclic objects. -/
def kInjective (𝒜 : DGA(𝒪)) : ObjectProperty (K ℤ Mod(𝒜, d)) :=
  (acyclic 𝒜).rightOrthogonal

/-- The full subcategory of K-injective objects in the intrinsic DG homotopy category. -/
abbrev KInjective (𝒜 : DGA(𝒪)) :=
  (kInjective 𝒜).FullSubcategory

namespace KInjective

/-- The canonical inclusion of K-injective objects into the intrinsic DG homotopy category. -/
abbrev ι (𝒜 : DGA(𝒪)) :
    KInjective 𝒜 ⥤ K ℤ Mod(𝒜, d) :=
  (kInjective 𝒜).ι

/-- The canonical inclusion of K-injective objects is fully faithful. -/
abbrev fullyFaithfulι (𝒜 : DGA(𝒪)) :
    (ι 𝒜).FullyFaithful :=
  (kInjective 𝒜).fullyFaithfulι

/-- A DG homotopy object is K-injective exactly when every morphism to it from an acyclic
object is zero. -/
theorem iff (𝒜 : DGA(𝒪)) (I : K ℤ Mod(𝒜, d)) :
    kInjective 𝒜 I ↔
      ∀ ⦃M : K ℤ Mod(𝒜, d)⦄ (f : M ⟶ I), acyclic 𝒜 M → f = 0 := sorry

/-- K-injective DG homotopy objects are precisely the local objects for
quasi-isomorphisms. -/
theorem eq_isLocal (𝒜 : DGA(𝒪)) :
    kInjective 𝒜 = (quasiIso 𝒜).isLocal := sorry

/-- Precomposition by a quasi-isomorphism is bijective on morphisms into a K-injective
target. -/
theorem precomp_bijective (𝒜 : DGA(𝒪))
    {M M' I : K ℤ Mod(𝒜, d)} (b : M ⟶ M')
    (hb : quasiIso 𝒜 b) (hI : kInjective 𝒜 I) :
    Function.Bijective (fun f : M' ⟶ I ↦ b ≫ f) := sorry

/-- A morphism between K-injective DG homotopy objects is a quasi-isomorphism exactly when it is
an isomorphism. -/
theorem quasiIso_iff_isIso (𝒜 : DGA(𝒪))
    {I I' : K ℤ Mod(𝒜, d)} (f : I ⟶ I')
    (hI : kInjective 𝒜 I) (hI' : kInjective 𝒜 I') :
    quasiIso 𝒜 f ↔ IsIso f := sorry

/-- Every integer shift of a K-injective DG homotopy object is K-injective. -/
theorem shift (𝒜 : DGA(𝒪)) (I : K ℤ Mod(𝒜, d))
    (hI : kInjective 𝒜 I) (n : ℤ) :
    kInjective 𝒜
      ((CategoryTheory.shiftFunctor (K ℤ Mod(𝒜, d)) n).obj I) := sorry

end KInjective

end


end SheafOfModules.RingedSite.DifferentialGradedModule.Homotopy
