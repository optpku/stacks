module

public import ReasLib.Algebra.Category.ModuleCat.Bimod.RelativeTensor.Functor
public import ReasLib.CategoryTheory.Adjunction.RightIso
public import ReasLib.CategoryTheory.Monoidal.Bimod.InternalHom.Linear
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.BraidedClosed
import Mathlib.Tactic.CrossRefAttribute

/-!
# Categorical relative tensor-Hom adjunctions in `ModuleCat`

This file specializes the generic relative tensor-Hom adjunction for bimodule objects to
ordinary modules.  Ordinary right `A`-modules are first realized as categorical modules; the
right adjoint is the generic relative internal Hom followed by extraction back to an ordinary
right `A`-module.  Thus the closed structure remains owned by the generic monoidal API.  As in
the underlying `ModuleCat` monoidal bridge, the rings and module carriers lie in one universe;
the concrete tensor-Hom API remains universe-polymorphic.
-/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

noncomputable section

universe u

namespace Module.Bimodule

variable {R A B N : Type u}
variable [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable [AddCommGroup N] [Module R N] [Module A N] [Module Bᵐᵒᵖ N]
variable [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N]
variable [SMulCommClass A Bᵐᵒᵖ N]

namespace InternalHom

/-- The generic categorical relative internal Hom out of `N`, extracted as an ordinary right
`A`-module. -/
@[stacks 09LN "categorical relative internal Hom functor"]
noncomputable abbrev categoricalFunctor (N : Type u) [AddCommGroup N] [Module R N]
    [Module A N] [Module Bᵐᵒᵖ N] [IsScalarTower R A N]
    [IsScalarTower R Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N] :
    CategoryTheory.Bimod.RightModule (algebraMon (R := R) B) ⥤ ModuleCat.{u} Aᵐᵒᵖ :=
  CategoryTheory.Bimod.InternalHom.functor
      (RightInternalHom.ofBraidedClosed (C := ModuleCat.{u} R))
      (toBimod (R := R) (A := A) (B := B) N) ⋙
    (rightModuleEquivalence (R := R) (A := A)).inverse

/-- The categorical relative internal-Hom functor is additive. -/
@[stacks 09LN "additive categorical relative internal Hom functor"]
instance categoricalFunctorAdditive :
    (categoricalFunctor (R := R) (A := A) (B := B) N).Additive := sorry

/-- The categorical relative internal-Hom functor is `R`-linear. -/
@[stacks 09LN "linear categorical relative internal Hom functor"]
instance categoricalFunctorLinear :
    Functor.Linear R
      (categoricalFunctor (R := R) (A := A) (B := B) N) := sorry

namespace Ordinary

/-- Ordinary relative internal Hom after extracting an ordinary right `B`-module from a
categorical one. -/
@[stacks 09LN "ordinary relative internal Hom on categorical right modules"]
noncomputable abbrev functor (N : Type u) [AddCommGroup N] [Module R N]
    [Module A N] [Module Bᵐᵒᵖ N] [IsScalarTower R A N]
    [IsScalarTower R Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N] :
    CategoryTheory.Bimod.RightModule (algebraMon (R := R) B) ⥤ ModuleCat.{u} Aᵐᵒᵖ :=
  (rightModuleEquivalence (R := R) (A := B)).inverse ⋙
    Module.Bimodule.InternalHom.functor (R := R) (A := A) (B := B) N

/-- Ordinary relative internal Hom on categorical right modules is additive. -/
@[stacks 09LN "additive ordinary relative internal Hom on categorical right modules"]
instance functorAdditive :
    (functor (R := R) (A := A) (B := B) N).Additive := sorry

/-- Ordinary relative internal Hom on categorical right modules is `R`-linear. -/
@[stacks 09LN "linear ordinary relative internal Hom on categorical right modules"]
instance functorLinear :
    Functor.Linear R (functor (R := R) (A := A) (B := B) N) := sorry

end Ordinary

end InternalHom

namespace RelativeTensor

/-- The categorical fixed-`N` relative tensor functor is left adjoint to the generic relative
internal Hom followed by ordinary-module extraction. -/
@[stacks 09LN "categorical relative tensor-Hom adjunction"]
noncomputable def categoricalAdjunction (N : Type u) [AddCommGroup N] [Module R N]
    [Module A N] [Module Bᵐᵒᵖ N] [IsScalarTower R A N]
    [IsScalarTower R Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N] :
    categoricalFunctor (R := R) (A := A) (B := B) N ⊣
      InternalHom.categoricalFunctor (R := R) (A := A) (B := B) N :=
  (rightModuleEquivalence (R := R) (A := A)).toAdjunction.comp
    (CategoryTheory.Bimod.InternalHom.adjunction
      (RightInternalHom.ofBraidedClosed (C := ModuleCat.{u} R))
      (toBimod (R := R) (A := A) (B := B) N))

namespace Ordinary

/-- The concrete relative tensor-Hom adjunction transported to categorical right
`B`-modules. -/
@[stacks 09LN "ordinary relative tensor-Hom adjunction on categorical right modules"]
noncomputable def adjunction (N : Type u) [AddCommGroup N] [Module R N]
    [Module A N] [Module Bᵐᵒᵖ N] [IsScalarTower R A N]
    [IsScalarTower R Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N] :
    functor (R := R) (A := A) (B := B) N ⊣
      InternalHom.Ordinary.functor (R := R) (A := A) (B := B) N :=
  (TensorHom.adjunction (R := R) (A := A) (B := B) N).comp
    (rightModuleEquivalence (R := R) (A := B)).toAdjunction

/-- Typeclass search recognizes ordinary relative tensoring followed by categorical
realization as a left adjoint. -/
@[stacks 09LN "ordinary relative tensor on categorical modules is a left adjoint"]
instance functorIsLeftAdjoint :
    (functor (R := R) (A := A) (B := B) N).IsLeftAdjoint := sorry

end Ordinary

/-- Typeclass search recognizes categorical relative tensoring with `N` as a left adjoint. -/
@[stacks 09LN "categorical relative tensor is a left adjoint"]
instance categoricalFunctorIsLeftAdjoint :
    (categoricalFunctor (R := R) (A := A) (B := B) N).IsLeftAdjoint := sorry

end RelativeTensor

namespace InternalHom

/-- Typeclass search recognizes categorical relative internal Hom out of `N` as a right
adjoint. -/
@[stacks 09LN "categorical relative internal Hom is a right adjoint"]
instance categoricalFunctorIsRightAdjoint :
    (categoricalFunctor (R := R) (A := A) (B := B) N).IsRightAdjoint := sorry

namespace Ordinary

/-- Typeclass search recognizes ordinary relative internal Hom on categorical right modules
as a right adjoint. -/
@[stacks 09LN "ordinary relative internal Hom on categorical modules is a right adjoint"]
instance functorIsRightAdjoint :
    (functor (R := R) (A := A) (B := B) N).IsRightAdjoint := sorry

/-- The categorical and ordinary relative internal-Hom functors agree as the right-adjoint
mates of the categorical-to-ordinary tensor comparison. -/
@[stacks 09LN "categorical and ordinary relative internal Hom functors"]
noncomputable def categoricalIso (N : Type u) [AddCommGroup N] [Module R N]
    [Module A N] [Module Bᵐᵒᵖ N] [IsScalarTower R A N]
    [IsScalarTower R Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N] :
    InternalHom.categoricalFunctor (R := R) (A := A) (B := B) N ≅
      functor (R := R) (A := A) (B := B) N :=
  Adjunction.rightAdjointIsoOfLeftIso
    (RelativeTensor.Ordinary.categoricalIso (R := R) (A := A) (B := B) N)
    (RelativeTensor.categoricalAdjunction (R := R) (A := A) (B := B) N)
    (RelativeTensor.Ordinary.adjunction (R := R) (A := A) (B := B) N)

/-- On ordinary right `B`-modules, categorical relative internal Hom agrees with the concrete
relative internal-Hom functor. -/
@[stacks 09LN "categorical internal Hom realized on ordinary modules"]
noncomputable def realizationIso (N : Type u) [AddCommGroup N] [Module R N]
    [Module A N] [Module Bᵐᵒᵖ N] [IsScalarTower R A N]
    [IsScalarTower R Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N] :
    rightModuleFunctor (R := R) (A := B) ⋙
        InternalHom.categoricalFunctor (R := R) (A := A) (B := B) N ≅
      Module.Bimodule.InternalHom.functor (R := R) (A := A) (B := B) N :=
  Functor.isoWhiskerLeft (rightModuleFunctor (R := R) (A := B))
      (categoricalIso (R := R) (A := A) (B := B) N) ≪≫
    (rightModuleEquivalence (R := R) (A := B)).funInvIdAssoc
      (Module.Bimodule.InternalHom.functor (R := R) (A := A) (B := B) N)

/-- The forward concrete realization comparison is the right-adjoint mate followed by
extraction-realization cancellation. -/
@[simp, stacks 09LN "forward categorical internal Hom realization comparison"]
theorem realizationIso_hom_app (P : ModuleCat.{u} Bᵐᵒᵖ) :
    (realizationIso (R := R) (A := A) (B := B) N).hom.app P =
      (categoricalIso (R := R) (A := A) (B := B) N).hom.app
          ((rightModuleFunctor (R := R) (A := B)).obj P) ≫
        (Module.Bimodule.InternalHom.functor
          (R := R) (A := A) (B := B) N).map
            ((rightModuleEquivalence (R := R) (A := B)).unitIso.inv.app P) := sorry

/-- The inverse concrete realization comparison first inserts extraction-realization and then
uses the inverse right-adjoint mate. -/
@[simp, stacks 09LN "inverse categorical internal Hom realization comparison"]
theorem realizationIso_inv_app (P : ModuleCat.{u} Bᵐᵒᵖ) :
    (realizationIso (R := R) (A := A) (B := B) N).inv.app P =
      (Module.Bimodule.InternalHom.functor
          (R := R) (A := A) (B := B) N).map
            ((rightModuleEquivalence (R := R) (A := B)).unitIso.hom.app P) ≫
        (categoricalIso (R := R) (A := A) (B := B) N).inv.app
          ((rightModuleFunctor (R := R) (A := B)).obj P) := sorry

end Ordinary

end InternalHom

namespace TensorHom

/-- Categorical currying, transported through the tensor and internal-Hom comparisons, is
the concrete tensor-Hom equivalence. -/
@[stacks 09LN "compatibility of categorical and ordinary tensor-Hom currying"]
theorem categoricalAdjunction_homEquiv_apply
    (M : ModuleCat.{u} Aᵐᵒᵖ) (P : ModuleCat.{u} Bᵐᵒᵖ)
    (f : (RelativeTensor.functor (R := R) (A := A) (B := B) N).obj M ⟶ P) :
    (RelativeTensor.categoricalAdjunction (R := R) (A := A) (B := B) N).homEquiv M
          ((rightModuleFunctor (R := R) (A := B)).obj P)
          ((RelativeTensor.Ordinary.categoricalIso
              (R := R) (A := A) (B := B) N).hom.app M ≫
            (rightModuleFunctor (R := R) (A := B)).map f) ≫
        (InternalHom.Ordinary.realizationIso
          (R := R) (A := A) (B := B) N).hom.app P =
      (adjunction (R := R) (A := A) (B := B) N).homEquiv M P f := sorry

/-- Inverse categorical currying agrees with inverse concrete currying under the tensor and
internal-Hom comparisons. -/
@[stacks 09LN "inverse compatibility of categorical and ordinary tensor-Hom currying"]
theorem categoricalAdjunction_homEquiv_symm_apply
    (M : ModuleCat.{u} Aᵐᵒᵖ) (P : ModuleCat.{u} Bᵐᵒᵖ)
    (g : M ⟶ (InternalHom.functor (R := R) (A := A) (B := B) N).obj P) :
    (RelativeTensor.Ordinary.categoricalIso
          (R := R) (A := A) (B := B) N).hom.app M ≫
        (rightModuleFunctor (R := R) (A := B)).map
          (((adjunction (R := R) (A := A) (B := B) N).homEquiv M P).symm g) =
      ((RelativeTensor.categoricalAdjunction
          (R := R) (A := A) (B := B) N).homEquiv M
            ((rightModuleFunctor (R := R) (A := B)).obj P)).symm
        (g ≫ (InternalHom.Ordinary.realizationIso
          (R := R) (A := A) (B := B) N).inv.app P) := sorry

/-- The categorical and concrete tensor-Hom units agree through the comparison
isomorphisms. -/
@[stacks 09LN "compatibility of categorical and ordinary tensor-Hom units"]
theorem categoricalAdjunction_unit_app (M : ModuleCat.{u} Aᵐᵒᵖ) :
    (RelativeTensor.categoricalAdjunction
          (R := R) (A := A) (B := B) N).unit.app M ≫
        (InternalHom.categoricalFunctor
          (R := R) (A := A) (B := B) N).map
            ((RelativeTensor.Ordinary.categoricalIso
              (R := R) (A := A) (B := B) N).hom.app M) ≫
        (InternalHom.Ordinary.realizationIso
          (R := R) (A := A) (B := B) N).hom.app
            ((RelativeTensor.functor (R := R) (A := A) (B := B) N).obj M) =
      (adjunction (R := R) (A := A) (B := B) N).unit.app M := sorry

/-- The categorical and concrete tensor-Hom counits agree through the comparison
isomorphisms. -/
@[stacks 09LN "compatibility of categorical and ordinary tensor-Hom counits"]
theorem categoricalAdjunction_counit_app (P : ModuleCat.{u} Bᵐᵒᵖ) :
    (RelativeTensor.Ordinary.categoricalIso
          (R := R) (A := A) (B := B) N).hom.app
            ((InternalHom.functor (R := R) (A := A) (B := B) N).obj P) ≫
        (rightModuleFunctor (R := R) (A := B)).map
          ((adjunction (R := R) (A := A) (B := B) N).counit.app P) =
      (RelativeTensor.categoricalFunctor
          (R := R) (A := A) (B := B) N).map
            ((InternalHom.Ordinary.realizationIso
              (R := R) (A := A) (B := B) N).inv.app P) ≫
        (RelativeTensor.categoricalAdjunction
          (R := R) (A := A) (B := B) N).counit.app
            ((rightModuleFunctor (R := R) (A := B)).obj P) := sorry

end TensorHom

#synth (RelativeTensor.categoricalFunctor
  (R := R) (A := A) (B := B) N).Additive
#synth Functor.Linear R
  (RelativeTensor.categoricalFunctor (R := R) (A := A) (B := B) N)
#synth (RelativeTensor.categoricalFunctor (R := R) (A := A) (B := B) N).IsLeftAdjoint
#synth (InternalHom.categoricalFunctor
  (R := R) (A := A) (B := B) N).Additive
#synth Functor.Linear R
  (InternalHom.categoricalFunctor (R := R) (A := A) (B := B) N)
#synth (InternalHom.categoricalFunctor (R := R) (A := A) (B := B) N).IsRightAdjoint
#synth (InternalHom.Ordinary.functor
  (R := R) (A := A) (B := B) N).Additive
#synth Functor.Linear R
  (InternalHom.Ordinary.functor (R := R) (A := A) (B := B) N)
#synth (RelativeTensor.Ordinary.functor
  (R := R) (A := A) (B := B) N).IsLeftAdjoint
#synth (InternalHom.Ordinary.functor
  (R := R) (A := A) (B := B) N).IsRightAdjoint

end Module.Bimodule
