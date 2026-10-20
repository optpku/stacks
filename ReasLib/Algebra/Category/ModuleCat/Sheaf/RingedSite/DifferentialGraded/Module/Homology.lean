/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Homotopy.Triangulated
public import ReasLib.Algebra.Homology.HomotopyCategory.Acyclic.Retract
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homology of differential graded module sheaves

This leaf defines all cohomology functors on the DG homotopy category by forgetting to the
ordinary cochain homotopy category.  It also owns the corresponding acyclic-object and
quasi-isomorphism predicates.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

-- Mathlib deliberately keeps this canonical construction non-global.  The homotopy-category
-- triangulation needs the resulting finite biproducts, so this owner pins it lexically.
attribute [local instance] Abelian.hasFiniteBiproducts

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule

section


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

namespace Homotopy

/-- The degree-`n` cohomology functor on the DG homotopy category of module sheaves. -/
@[stacks 0FT2]
noncomputable def homologyFunctor (𝒜 : DGA(𝒪)) (n : ℤ) :
    K ℤ Mod(𝒜, d) ⥤ ringedSiteModuleCategory J 𝒪 :=
  forget 𝒜 ⋙
    HomotopyCategory.homologyFunctor (ringedSiteModuleCategory J 𝒪) (up ℤ) n

namespace Homology

/-- DG-module cohomology factors the cohomology of the underlying cochain complex through the
DG homotopy category. -/
@[stacks 0FT2]
noncomputable def factors (𝒜 : DGA(𝒪)) (n : ℤ) :
    toK 𝒜 ⋙ homologyFunctor 𝒜 n ≅
      forgetToComplex 𝒜 ⋙
        HomologicalComplex.homologyFunctor
          (ringedSiteModuleCategory J 𝒪) (up ℤ) n :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (forgetFactors 𝒜)
      (HomotopyCategory.homologyFunctor
        (ringedSiteModuleCategory J 𝒪) (up ℤ) n) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (forgetToComplex 𝒜)
      (HomotopyCategory.homologyFunctorFactors
        (ringedSiteModuleCategory J 𝒪) (up ℤ) n)

/-- The forward component of the DG-module cohomology factorization is Mathlib's standard
homotopy-category cohomology comparison. -/
theorem factors_hom_app (𝒜 : DGA(𝒪)) (n : ℤ) (M : Mod(𝒜, d)) :
    (factors 𝒜 n).hom.app M =
      (HomotopyCategory.homologyFunctorFactors
        (ringedSiteModuleCategory J 𝒪) (up ℤ) n).hom.app
        M.toComplex := sorry

/-- The inverse component of the DG-module cohomology factorization is Mathlib's standard
inverse cohomology comparison. -/
theorem factors_inv_app (𝒜 : DGA(𝒪)) (n : ℤ) (M : Mod(𝒜, d)) :
    (factors 𝒜 n).inv.app M =
      (HomotopyCategory.homologyFunctorFactors
        (ringedSiteModuleCategory J 𝒪) (up ℤ) n).inv.app
        M.toComplex := sorry

/-- DG-module cohomology is canonically the cohomology of the underlying cochain complex. -/
noncomputable def objIso (𝒜 : DGA(𝒪)) (n : ℤ)
    (X : K ℤ Mod(𝒜, d)) :
    (homologyFunctor 𝒜 n).obj X ≅ X.obj.toComplex.homology n :=
  (HomotopyCategory.homologyFunctorFactors
    (ringedSiteModuleCategory J 𝒪) (up ℤ) n).app X.obj.toComplex

/-- The object comparison for DG-module cohomology is the standard comparison attached to
the homotopy-category quotient. -/
theorem objIso_eq (𝒜 : DGA(𝒪)) (n : ℤ)
    (X : K ℤ Mod(𝒜, d)) :
    objIso 𝒜 n X =
      (HomotopyCategory.homologyFunctorFactors
        (ringedSiteModuleCategory J 𝒪) (up ℤ) n).app
        X.obj.toComplex := sorry

/-- Naturality of `objIso` computes the map on a represented DG homotopy class as
the ordinary homology map of its underlying cochain map. -/
theorem objIso_naturality_rep
    (𝒜 : DGA(𝒪)) (n : ℤ) {L M : Mod(𝒜, d)} (f : CompHom L M) :
    (homologyFunctor 𝒜 n).map f.toHomotopyClass ≫
        (objIso 𝒜 n ⟨M⟩).hom =
      (objIso 𝒜 n ⟨L⟩).hom ≫
        (HomologicalComplex.homologyFunctor
          (ringedSiteModuleCategory J 𝒪) (up ℤ) n).map
          (compHomToHom f).toCochainMap := sorry

/-- Every degreewise DG-module cohomology functor is homological. -/
@[stacks 0FT2]
instance isHomological (𝒜 : DGA(𝒪)) (n : ℤ) :
    (homologyFunctor 𝒜 n).IsHomological := sorry

/-- The canonical shift sequence whose degree-`n` term is DG-module cohomology in degree
`n`. -/
noncomputable instance zeroShiftSequence (𝒜 : DGA(𝒪)) :
    (homologyFunctor 𝒜 0).ShiftSequence ℤ :=
  Functor.ShiftSequence.leftComp (F := homologyFunctor 𝒜 0)
    (π := forget 𝒜)
    (H := HomotopyCategory.homologyFunctor
      (ringedSiteModuleCategory J 𝒪) (up ℤ) 0)
    (Iso.refl _) ℤ

/-- The degree-`n` term of the canonical shift sequence is the degree-`n` DG-module
cohomology functor. -/
theorem shift (𝒜 : DGA(𝒪)) (n : ℤ) :
    (homologyFunctor 𝒜 0).shift n = homologyFunctor 𝒜 n := sorry

end Homology

/-- A DG-module homotopy object is acyclic when its underlying cochain homotopy object is
homology-acyclic. -/
@[stacks 0FT3]
def acyclic (𝒜 : DGA(𝒪)) : ObjectProperty (K ℤ Mod(𝒜, d)) :=
  (homologyFunctor 𝒜 0).homologicalKernel

namespace Acyclic

/-- A DG-module homotopy object is acyclic exactly when all its cohomology objects vanish. -/
theorem iff (𝒜 : DGA(𝒪)) (X : K ℤ Mod(𝒜, d)) :
    acyclic 𝒜 X ↔
      ∀ n : ℤ, IsZero ((homologyFunctor 𝒜 n).obj X) := sorry

/-- A DG-module homotopy object is acyclic exactly when its underlying cochain complex is
acyclic. -/
theorem underlying_iff (𝒜 : DGA(𝒪)) (X : K ℤ Mod(𝒜, d)) :
    acyclic 𝒜 X ↔ X.obj.toComplex.Acyclic := sorry

/-- Acyclic DG-module homotopy objects form a triangulated subcategory. -/
@[stacks 0FT3]
instance isTriangulated (𝒜 : DGA(𝒪)) :
    (acyclic 𝒜).IsTriangulated := sorry

/-- Acyclic DG-module homotopy objects are closed under isomorphisms. -/
@[stacks 0FT3]
instance isClosedUnderIsomorphisms (𝒜 : DGA(𝒪)) :
    (acyclic 𝒜).IsClosedUnderIsomorphisms := sorry

/-- Acyclic DG-module homotopy objects are stable under retracts. -/
@[stacks 0FT3]
instance isStableUnderRetracts (𝒜 : DGA(𝒪)) :
    (acyclic 𝒜).IsStableUnderRetracts := sorry

end Acyclic

/-- A morphism in the DG homotopy category is a quasi-isomorphism when it induces an
isomorphism on cohomology in every degree. -/
def quasiIso (𝒜 : DGA(𝒪)) : MorphismProperty (K ℤ Mod(𝒜, d)) :=
  (HomotopyCategory.quasiIso
    (ringedSiteModuleCategory J 𝒪) (up ℤ)).inverseImage
    (forget 𝒜)

namespace QuasiIso

/-- Membership in `quasiIso 𝒜` is degreewise invertibility on cohomology. -/
theorem iff (𝒜 : DGA(𝒪)) {X Y : K ℤ Mod(𝒜, d)} (f : X ⟶ Y) :
    quasiIso 𝒜 f ↔
      ∀ n : ℤ, IsIso ((homologyFunctor 𝒜 n).map f) := sorry

/-- DG-module quasi-isomorphisms are exactly the morphisms whose triangulated cone is
acyclic. -/
theorem eq_trW (𝒜 : DGA(𝒪)) :
    quasiIso 𝒜 = (acyclic 𝒜).trW := sorry

/-- A DG-module homotopy morphism is a quasi-isomorphism exactly when it belongs to the
triangulated weak-equivalence class generated by acyclic objects. -/
theorem iff_trW (𝒜 : DGA(𝒪)) {X Y : K ℤ Mod(𝒜, d)} (f : X ⟶ Y) :
    quasiIso 𝒜 f ↔ (acyclic 𝒜).trW f := sorry

/-- DG-module quasi-isomorphisms contain all isomorphisms. -/
instance containsIdentities (𝒜 : DGA(𝒪)) :
    (quasiIso 𝒜).ContainsIdentities := sorry

/-- DG-module quasi-isomorphisms are closed under composition. -/
instance isMultiplicative (𝒜 : DGA(𝒪)) :
    (quasiIso 𝒜).IsMultiplicative := sorry

/-- DG-module quasi-isomorphisms satisfy the two-out-of-three property. -/
instance hasTwoOutOfThree (𝒜 : DGA(𝒪)) :
    (quasiIso 𝒜).HasTwoOutOfThreeProperty := sorry

/-- DG-module quasi-isomorphisms are stable under retracts. -/
instance isStableUnderRetracts (𝒜 : DGA(𝒪)) :
    (quasiIso 𝒜).IsStableUnderRetracts := sorry

/-- DG-module quasi-isomorphisms are compatible with every integer shift. -/
instance isCompatibleWithShift (𝒜 : DGA(𝒪)) :
    (quasiIso 𝒜).IsCompatibleWithShift ℤ := sorry

end QuasiIso

end Homotopy

end


end SheafOfModules.RingedSite.DifferentialGradedModule
