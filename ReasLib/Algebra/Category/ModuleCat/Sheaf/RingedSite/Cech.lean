/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Over
import Mathlib.Tactic.CrossRefAttribute

/-!
# Čech complexes for modules on a ringed site

This leaf owns the coefficient-sensitive part of the Čech construction.  The covering family is
an indexed family in the slice `Over U`; the construction first changes scalars from the values of
the ring sheaf to the base ring `𝒪(U)`, and then uses Mathlib's coefficient-independent
`CategoryTheory.cechComplexFunctor`.

The owner is deliberately site-generic.  Ringed spaces and other geometric sites should only
provide the specialization of the ring sheaf and the chosen family.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits
open CategoryTheory.Limits.FormalCoproduct

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Forgetting the sheaf condition preserves the preadditive structure on module sheaves. -/
noncomputable instance forget_additive (𝒪 : Sheaf J RingCat) :
    (SheafOfModules.forget 𝒪).Additive := sorry

/- The identity object of `Over U` is terminal, hence its opposite is initial. -/

/-- The canonical initial object used to view every presheaf module on `C` as a presheaf of
`𝒪(U)`-modules on `Over U`. -/
abbrev overInitial (U : C) :
    Limits.IsInitial (op (Over.mk (𝟙 U))) :=
  Over.mkIdTerminal.op

/-- The presheaf on `Over U` of `𝒪(U)`-modules obtained from a presheaf of `𝒪`-modules by
restriction of scalars along the maps `𝒪(U) ⟶ 𝒪(V)`. -/
@[stacks 01EI "ringed-site sections on a slice"]
abbrev sectionsOnOver
    (𝒪 : Sheaf J RingCat) (U : C) :
    PresheafOfModules.{w} 𝒪.obj ⥤
      (Over U)ᵒᵖ ⥤ ModuleCat.{w} (𝒪.obj.obj (op U)) :=
  PresheafOfModules.pushforward₀ (Over.forget U) 𝒪.obj ⋙
    PresheafOfModules.forgetToPresheafModuleCat
      (op (Over.mk (𝟙 U))) (overInitial U)

/-- The Čech cochain-complex functor for a presheaf of `𝒪`-modules and an indexed family in
`Over U`.  The coefficient ring is `𝒪(U)`, obtained by restriction of scalars before applying
Mathlib's canonical `cechComplexFunctor`. -/
@[stacks 01EI "ringed-site module Cech complex"]
abbrev cechComplex
    (𝒪 : Sheaf J RingCat) (U : C)
    [HasFiniteProducts (Over U)] {ι : Type w} (family : ι → Over U) :
    PresheafOfModules.{w} 𝒪.obj ⥤
      CochainComplex (ModuleCat.{w} (𝒪.obj.obj (op U))) ℕ :=
  sectionsOnOver 𝒪 U ⋙ cechComplexFunctor family

/-- The ringed-site module Cech complex is additive in its coefficient module.  This is the
canonical support instance used by ringed-space specializations and their totalizations. -/
@[stacks 00ZY "additivity of the ringed-site module Cech complex"]
noncomputable instance cechComplex_additive
    (𝒪 : Sheaf J RingCat) (U : C)
    [HasFiniteProducts (Over U)] {ι : Type w} (family : ι → Over U) :
    (cechComplex 𝒪 U family).Additive := sorry

/-- The degree-`p` Čech cohomology object of a presheaf of `𝒪`-modules on a ringed site. -/
@[stacks 01EI "ringed-site module Cech cohomology"]
abbrev cechCohomology
    (𝒪 : Sheaf J RingCat) (U : C)
    [HasFiniteProducts (Over U)] {ι : Type w} (family : ι → Over U)
    (M : PresheafOfModules.{w} 𝒪.obj) (p : ℕ) :
    ModuleCat.{w} (𝒪.obj.obj (op U)) :=
  (HomologicalComplex.homologyFunctor
      (ModuleCat.{w} (𝒪.obj.obj (op U))) (ComplexShape.up ℕ) p).obj
    ((cechComplex 𝒪 U family).obj M)

namespace Cech

section SheafCohomology

variable (𝒪 : Sheaf J RingCat) (U : C) [HasFiniteProducts (Over U)]
variable {ι : Type w} (family : ι → Over U)

/-- For a covering family, degree-zero Čech cohomology of a sheaf module is its module of
sections over the covered object. -/
@[stacks 03FC "degree-zero module Cech cohomology"]
theorem zero_isomorphic_evaluation
    (hfamily : (J.over U).CoversTop family) (F : SheafOfModules 𝒪) :
    IsIsomorphic (cechCohomology 𝒪 U family ((SheafOfModules.forget 𝒪).obj F) 0)
      ((SheafOfModules.evaluation 𝒪 (op U)).obj F) := sorry

/-- Positive successor degrees of Čech cohomology vanish on injective sheaf modules. -/
@[stacks 03FC "injective module Cech acyclicity"]
theorem isZero_of_injective_succ
    (I : SheafOfModules 𝒪) [Injective I] (p : ℕ) :
    IsZero (cechCohomology 𝒪 U family ((SheafOfModules.forget 𝒪).obj I) (p + 1)) := sorry

/-- Every positive-degree Čech cohomology object of an injective sheaf module is zero. -/
theorem isZero_of_injective_of_pos
    (I : SheafOfModules 𝒪) [Injective I] (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology 𝒪 U family ((SheafOfModules.forget 𝒪).obj I) p) := sorry

end SheafCohomology

variable {D : Type u} [Category.{u} D] {K : GrothendieckTopology D}
variable (𝒪 : Sheaf K RingCat) (U : D) [HasFiniteProducts (Over U)]
variable {ι : Type u} (family : ι → Over U)

/-- The index set of the degree-`n` intersections in the Čech nerve of `family`. -/
@[stacks 01EL "Cech intersection indices"]
abbrev Index (n : ℕ) :=
  ((FormalCoproduct.mk _ family).cech.obj (op (SimplexCategory.mk n))).I

/-- The underlying site object of a degree-`n` intersection in the Čech nerve. -/
@[stacks 01EL "Cech intersection objects"]
abbrev intersection (n : ℕ) (i : Index U family n) : D :=
  ((FormalCoproduct.mk _ family).cech.obj (op (SimplexCategory.mk n))).obj i |>.left

/-- The free representable presheaf module associated with one Čech intersection. -/
@[stacks 01EL "free module on a Cech intersection"]
noncomputable abbrev freeSummand (n : ℕ) (i : Index U family n) :
    PresheafOfModules.{u} 𝒪.obj :=
  (yoneda ⋙ PresheafOfModules.free 𝒪.obj).obj (intersection U family n i)

/-- The simplicial presheaf module obtained by evaluating the underlying Čech nerve on free
representables. -/
@[stacks 01EL "free simplicial module of a ringed-site Cech family"]
noncomputable abbrev freeSimplicial :
    SimplicialObject (PresheafOfModules.{u} 𝒪.obj) :=
  (FormalCoproduct.mk _ family).cech ⋙ FormalCoproduct.forgetOver U ⋙
    (FormalCoproduct.eval D (PresheafOfModules.{u} 𝒪.obj)).obj
      (yoneda ⋙ PresheafOfModules.free 𝒪.obj)

/-- The alternating-face chain complex of free representable presheaf modules attached to a
family in `Over U`. -/
@[stacks 01EL "free chain complex of a ringed-site Cech family"]
noncomputable abbrev freeChain :
    ChainComplex (PresheafOfModules.{u} 𝒪.obj) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj (freeSimplicial 𝒪 U family)

/-- The degree-`n` term of `freeChain` is the coproduct of its free representable intersection
summands. -/
theorem freeChain_degree (n : ℕ) :
    (freeChain 𝒪 U family).X n = ∐ fun i : Index U family n ↦ freeSummand 𝒪 U family n i := sorry

/-- The cochain-complex functor represented by the free Čech chain complex. -/
@[stacks 01EL "represented Hom complex of a ringed-site Cech family"]
noncomputable abbrev homFunctor :
    PresheafOfModules.{u} 𝒪.obj ⥤ CochainComplex AddCommGrpCat.{u} ℕ :=
  (((preadditiveCoyoneda.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (freeChain 𝒪 U family).op).asFunctor)

/-- The module-valued Čech complex, viewed degreewise in additive commutative groups. -/
@[stacks 01EL "underlying additive ringed-site Cech complex"]
noncomputable abbrev additiveComplex :
    PresheafOfModules.{u} 𝒪.obj ⥤ CochainComplex AddCommGrpCat.{u} ℕ :=
  cechComplex 𝒪 U family ⋙
    (forget₂ (ModuleCat.{u} (𝒪.obj.obj (op U))) AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.up ℕ)

/-- The module of sections on one degree-`n` Čech intersection. -/
abbrev moduleSummand (F : PresheafOfModules.{u} 𝒪.obj) (n : ℕ) (i : Index U family n) :
    ModuleCat.{u} (𝒪.obj.obj (op U)) :=
  ((sectionsOnOver 𝒪 U).obj F).obj
    (op (((FormalCoproduct.mk _ family).cech.obj (op (SimplexCategory.mk n))).obj i))

/-- The underlying additive group of sections on one degree-`n` Čech intersection. -/
abbrev additiveSummand (F : PresheafOfModules.{u} 𝒪.obj) (n : ℕ) (i : Index U family n) :
    AddCommGrpCat.{u} :=
  (forget₂ (ModuleCat.{u} (𝒪.obj.obj (op U))) AddCommGrpCat.{u}).obj
    (moduleSummand 𝒪 U family F n i)

/-- Evaluation on an intersection and the corresponding restricted-scalar section group are
canonically the same additive group. -/
theorem freeYonedaTarget_eq (F : PresheafOfModules.{u} 𝒪.obj)
    (n : ℕ) (i : Index U family n) :
    AddCommGrpCat.of (F.obj (op (intersection U family n i))) =
      additiveSummand 𝒪 U family F n i := sorry

/-- The canonical identification used as the target of the free Yoneda comparison. -/
noncomputable abbrev freeYonedaTargetIso (F : PresheafOfModules.{u} 𝒪.obj)
    (n : ℕ) (i : Index U family n) :
    AddCommGrpCat.of (F.obj (op (intersection U family n i))) ≅
      additiveSummand 𝒪 U family F n i :=
  eqToIso (freeYonedaTarget_eq 𝒪 U family F n i)

/-- The free-Yoneda comparison on one intersection summand. -/
@[stacks 01EL "free-Yoneda Cech component"]
noncomputable def degreeComponent (F : PresheafOfModules.{u} 𝒪.obj)
    (n : ℕ) (i : Index U family n) :
    AddCommGrpCat.of ((freeChain 𝒪 U family).X n ⟶ F) ⟶
      additiveSummand 𝒪 U family F n i :=
  let f : AddCommGrpCat.of ((freeChain 𝒪 U family).X n ⟶ F) →
      additiveSummand 𝒪 U family F n i := fun α ↦ PresheafOfModules.freeYonedaEquiv
          (Sigma.ι (fun j : Index U family n ↦ freeSummand 𝒪 U family n j) i ≫
            eqToHom (freeChain_degree 𝒪 U family n).symm ≫ α)
  let hmap : f 0 = 0 ∧ ∀ α β, f (α + β) = f α + f β := sorry
  AddCommGrpCat.ofHom { toFun := f, map_zero' := hmap.1, map_add' := hmap.2 } ≫
    (freeYonedaTargetIso 𝒪 U family F n i).hom

/-- The degree-`n` term of the module-valued Čech complex is its product of intersection
section modules. -/
theorem moduleComplex_degree (F : PresheafOfModules.{u} 𝒪.obj) (n : ℕ) :
    ((cechComplex 𝒪 U family).obj F).X n =
      ∏ᶜ fun i : Index U family n ↦ moduleSummand 𝒪 U family F n i := sorry

/-- Forgetting coefficients identifies the degree-`n` Čech term with the product of its
underlying additive section groups. -/
noncomputable def additiveDegreeIso (F : PresheafOfModules.{u} 𝒪.obj) (n : ℕ) :
    (∏ᶜ fun i : Index U family n ↦ additiveSummand 𝒪 U family F n i) ≅
      ((additiveComplex 𝒪 U family).obj F).X n :=
  (PreservesProduct.iso
      (forget₂ (ModuleCat.{u} (𝒪.obj.obj (op U))) AddCommGrpCat.{u})
      (fun i : Index U family n ↦ moduleSummand 𝒪 U family F n i)).symm ≪≫
    eqToIso (by
      simpa [additiveComplex] using congrArg
        (forget₂ (ModuleCat.{u} (𝒪.obj.obj (op U))) AddCommGrpCat.{u}).obj
        (moduleComplex_degree 𝒪 U family F n).symm)

/-- The canonical degreewise map from represented Hom to Čech cochains. -/
@[stacks 01EL "degreewise Hom-to-Cech comparison"]
noncomputable def degreeComparison (F : PresheafOfModules.{u} 𝒪.obj) (n : ℕ) :
    ((homFunctor 𝒪 U family).obj F).X n ⟶ ((additiveComplex 𝒪 U family).obj F).X n :=
  Pi.lift (fun i : Index U family n ↦ degreeComponent 𝒪 U family F n i) ≫
    (additiveDegreeIso 𝒪 U family F n).hom

/-- The comparison on one coefficient presheaf, with differential compatibility separated as a
proof field from the explicit free-Yoneda maps. -/
noncomputable def homComparisonApp (F : PresheafOfModules.{u} 𝒪.obj) :
    (homFunctor 𝒪 U family).obj F ⟶ (additiveComplex 𝒪 U family).obj F where
  f n := degreeComparison 𝒪 U family F n
  comm' _ _ := sorry

/-- The canonical natural comparison from the complex represented by the free Čech chain complex
to Čech cochains. -/
@[stacks 01EL "canonical Hom-to-Cech comparison"]
noncomputable def homComparison :
    homFunctor 𝒪 U family ⟶ additiveComplex 𝒪 U family where
  app F := homComparisonApp 𝒪 U family F
  naturality _ _ _ := sorry

/-- The comparison is given in degree `n` by the product of the free-Yoneda component maps. -/
@[simp]
theorem homComparison_f (F : PresheafOfModules.{u} 𝒪.obj) (n : ℕ) :
    ((homComparison 𝒪 U family).app F).f n = degreeComparison 𝒪 U family F n := sorry

/-- The canonical morphism-complex comparison is an isomorphism of cochain-complex functors. -/
@[stacks 01EL "morphism-complex comparison is an isomorphism"]
theorem homComparison_isIso : IsIso (homComparison 𝒪 U family) := sorry

/-- The reusable typeclass instance for the canonical morphism-complex comparison. -/
noncomputable instance homComparisonIsIso : IsIso (homComparison 𝒪 U family) :=
  homComparison_isIso 𝒪 U family

/-- The represented morphism complex from the free Čech chain complex is naturally isomorphic to
the underlying additive Čech complex. -/
@[stacks 01EL "morphism complex from the Cech chain complex computes Cech cochains"]
noncomputable abbrev homComparisonIso :
    homFunctor 𝒪 U family ≅ additiveComplex 𝒪 U family :=
  asIso (homComparison 𝒪 U family)

end Cech



end SheafOfModules.RingedSite

end
