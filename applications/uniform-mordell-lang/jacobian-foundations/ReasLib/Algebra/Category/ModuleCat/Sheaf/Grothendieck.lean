module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import ReasLib.CategoryTheory.Abelian.FunctorialInjectives.Grothendieck
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.GrothendieckLarge
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.GrothendieckUniverse
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u v r w

namespace SheafOfModules

/-- Forgetting a sheaf of modules over a ring sheaf to its underlying additive sheaf
preserves all small limits. -/
@[stacks 03DB "limits", instance]
theorem toSheaf_preservesLimits
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (𝒪 : Sheaf J RingCat.{max u v}) :
    PreservesLimits (toSheaf.{max u v} 𝒪) := sorry

/-- Forgetting a sheaf of modules over a ring sheaf to its underlying additive sheaf
preserves all small colimits when additive sheafification is available. -/
@[stacks 03DB "colimits", instance]
theorem toSheaf_preservesColimits
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (𝒪 : Sheaf J RingCat.{max u v})
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] :
    PreservesColimits (toSheaf.{max u v} 𝒪) := sorry

/-- The forgetful functor from sheaves of modules to additive sheaves is exact. -/
@[stacks 03DA]
theorem toSheaf_exact
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (𝒪 : Sheaf J RingCat.{max u v})
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] :
    exactFunctor (SheafOfModules.{max u v} 𝒪)
      (Sheaf J AddCommGrpCat.{max u v}) (toSheaf.{max u v} 𝒪) := sorry

/-- The category of sheaves of modules over a ring sheaf satisfies `AB5` when additive
sheafification is available. -/
@[stacks 03DB "filtered colimits", instance]
theorem hasAB5
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (𝒪 : Sheaf J RingCat.{max u v})
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasSheafify J AddCommGrpCat.{max u v}] :
    AB5 (SheafOfModules.{max u v} 𝒪) := sorry

/-- Sheaves of modules over a ring sheaf admit a separator. -/
instance hasSeparator
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (𝒪 : Sheaf J RingCat.{max u v}) :
    HasSeparator (SheafOfModules.{max u v} 𝒪) :=
  ⟨LargeSite.generator J 𝒪, LargeSite.generator_isSeparator J 𝒪⟩

/-- Sheaves of modules over a ring sheaf form a Grothendieck abelian category. -/
@[stacks 0142, stacks 01DU "Grothendieck-abelian owner"]
instance isGrothendieckAbelian
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (𝒪 : Sheaf J RingCat.{max u v}) :
    IsGrothendieckAbelian.{max u v} (SheafOfModules.{max u v} 𝒪) :=
  LargeSite.grothendieck J 𝒪

/-- The universe-lifted form is the canonical owner used when module coefficients live in a
larger universe than the site. -/
instance isGrothendieckAbelian_of_univLE
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [UnivLE.{max u v r, w}]
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (𝒪 : Sheaf J RingCat.{r}) :
    IsGrothendieckAbelian.{w} (SheafOfModules.{w} 𝒪) := by
  -- The given universe bound contains the object index of the component maps.
  letI : Small.{w} C :=
    @Small.trans_univLE.{max u v r, w, u} C (small_max.{max v r} C) inferInstance
  exact
    { locallySmall :=
        { hom_small M N := small_of_injective
            (f := fun f : M ⟶ N ↦ fun V : Cᵒᵖ ↦
              fun x : M.val.obj V ↦ f.val.app V x)
            (by
              intro f g h
              ext V x
              exact congrFun (congrFun h V) x) }
      ab5OfSize := sorry
      hasSeparator := ⟨generatorOfUnivLE 𝒪, generatorOfUnivLE_isSeparator 𝒪⟩ }

/-- Sheaves of modules over a ring sheaf admit a functorial choice of monomorphisms into
injective objects. -/
@[stacks 01DI "ringed-space specialization", stacks 01DU]
noncomputable instance hasFunctorialInjectives
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (𝒪 : Sheaf J RingCat.{max u v}) :
    HasFunctorialInjectives (SheafOfModules.{max u v} 𝒪) := by
  -- Local instance justification: use the actual generator at this coefficient universe.
  letI := isGrothendieckAbelian 𝒪
  exact IsGrothendieckAbelian.hasFunctorialInjectives

end SheafOfModules
