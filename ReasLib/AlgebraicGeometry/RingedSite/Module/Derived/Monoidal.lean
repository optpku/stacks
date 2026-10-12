/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KFlatResolution
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat.Coproduct
public import ReasLib.Algebra.Homology.DerivedCategory.Monoidal.KFlat.TermwiseFlat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Monoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# The canonical derived tensor product on a commutative ringed site

This file assembles the K-flat localization model for derived module sheaves over a commutative
ring sheaf `O` on a site `J`. A general `RingedSite` has only a sheaf of possibly noncommutative
rings, so its module category does not carry this tensor product canonically. The public API is
therefore indexed by the canonical presentation `RingedSite.ofCommRingSheaf J O`.

The three localization conditions remain explicit proof boundaries: placeholder proofs of them
must not be installed globally because localization uses those proofs to choose functor and
inverse data.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open SheafOfModules.RingedSite (ringedSiteModuleCategory)

noncomputable section

universe u v w

namespace RingedSite.Hom.ModuleDerived

set_option checkBinderAnnotations false

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable (O : Sheaf J CommRingCat.{w})

namespace KFlat

/-- The condition that totalized tensoring over `O` descends from cochain complexes of module
sheaves to their homotopy category. -/
@[stacks 0FPB "commutative ringed-site homotopy tensor-descends condition"]
abbrev HomotopyTensorDescends : Prop :=
  HomotopyCategory.Koszul.TensorDescends
    (C := ringedSiteModuleCategory.{u, v, w, w} J O)

/-- The condition that tensoring K-flat homotopy objects over `O` preserves the restricted
quasi-isomorphisms. -/
@[stacks 0FPB "commutative ringed-site K-flat tensor-descends condition"]
abbrev TensorDescends [HomotopyTensorDescends O] : Prop :=
  HomotopyCategory.KFlat.TensorDescends
    (C := ringedSiteModuleCategory.{u, v, w, w} J O)

/-- The condition that K-flat homotopy objects over `O` localize to the derived category of
module sheaves. -/
@[stacks 0FPB "commutative ringed-site K-flat localization condition"]
abbrev IsLocalization : Prop :=
  @CategoryTheory.DerivedCategory.KFlat.IsLocalization
    (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
    (moduleCat_hasDerivedCategory (RingedSite.ofCommRingSheaf J O)) _ _

namespace TermwiseFlat

/-- The canonical functor from K-flat, termwise-flat homotopy models of `O`-modules to their
derived category. -/
@[stacks 06YS "ringed-site good flat model localization"]
noncomputable abbrev localizationFunctor :
    HomotopyCategory.KFlat.TermwiseFlat
        (ringedSiteModuleCategory.{u, v, w, w} J O) ⥤
      ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O) :=
  @CategoryTheory.DerivedCategory.KFlat.TermwiseFlat.localizationFunctor
    (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
    (moduleCat_hasDerivedCategory (RingedSite.ofCommRingSheaf J O)) _ _

/-- The good-flat-model localization agrees with inclusion in the homotopy category followed by
the standard localization of module complexes. -/
@[stacks 06YS "ringed-site good flat model localization comparison"]
noncomputable def localizationFunctorIso :
    localizationFunctor O ≅
      (HomotopyCategory.KFlat.termwiseFlat
        (ringedSiteModuleCategory.{u, v, w, w} J O)).ι ⋙
        moduleLocalization.{w} (RingedSite.ofCommRingSheaf J O) :=
  @CategoryTheory.DerivedCategory.KFlat.TermwiseFlat.localizationFunctorIso
    (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
    (moduleCat_hasDerivedCategory (RingedSite.ofCommRingSheaf J O)) _ _

/-- The condition that good flat homotopy models of `O`-modules present their derived
category. -/
@[stacks 06YS "ringed-site good flat model localization condition"]
abbrev IsLocalization : Prop :=
  @CategoryTheory.DerivedCategory.KFlat.TermwiseFlat.IsLocalization
    (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
    (moduleCat_hasDerivedCategory (RingedSite.ofCommRingSheaf J O)) _ _

/-- K-flat complexes of `O`-modules with flat terms form a localization model for the derived
category. This remains a theorem rather than an instance so its deferred proof cannot select
downstream localization data. -/
@[stacks 06YS "ringed-site good flat models present the derived category"]
theorem localizationIsLocalization : IsLocalization O := sorry

end TermwiseFlat

end KFlat

/-- The derived category of modules over `O` carries the tensor product obtained by localizing
K-flat complexes. -/
@[stacks 0FPB "commutative ringed-site derived tensor product",
  stacks 0FPT "derived tensor product", implicit_reducible]
noncomputable def monoidalCategory
    [KFlat.HomotopyTensorDescends O] [KFlat.TensorDescends O]
    [KFlat.IsLocalization O] :
    MonoidalCategory (ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) :=
  @CategoryTheory.DerivedCategory.KFlat.monoidalCategory
    (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
    (moduleCat_hasDerivedCategory (RingedSite.ofCommRingSheaf J O)) _ _ _ _ _ _ _ _ _ _

/-- The K-flat derived tensor product of module sheaves over `O` is symmetric. -/
@[stacks 0FPB "commutative ringed-site symmetric derived tensor product",
  stacks 0FPT "symmetric derived tensor product", implicit_reducible]
noncomputable def symmetricCategory
    [KFlat.HomotopyTensorDescends O] [KFlat.TensorDescends O]
    [KFlat.IsLocalization O] :
    SymmetricCategory (ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) :=
  @CategoryTheory.DerivedCategory.KFlat.symmetricCategory
    (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
    (moduleCat_hasDerivedCategory (RingedSite.ofCommRingSheaf J O)) _ _ _ _ _ _ _ _ _ _

end RingedSite.Hom.ModuleDerived
