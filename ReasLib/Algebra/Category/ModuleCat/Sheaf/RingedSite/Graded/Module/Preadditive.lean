module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Module

/-!
# Preadditive graded module sheaves

The additive operations on graded module morphisms are computed in every degree using the
existing additive structure on module-sheaf morphisms. They do not require sheafification.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.GradedModuleSheaf

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.GradedModuleSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {ι : Type} [AddMonoid ι]

/-- The zero graded-module morphism is computed in every degree. -/
instance instZeroHom {𝒜 : GradedAlgebraSheaf 𝒪 ι} (M N : Mod(𝒜)) : Zero (Hom M N) where
  zero :=
    { hom := fun _ ↦ 0
      comm := sorry }

/-- Addition of graded-module morphisms is computed in every degree. -/
instance instAddHom {𝒜 : GradedAlgebraSheaf 𝒪 ι} (M N : Mod(𝒜)) : Add (Hom M N) where
  add f g :=
    { hom := fun n ↦ f.hom n + g.hom n
      comm := sorry }

/-- Negation of graded-module morphisms is computed in every degree. -/
instance instNegHom {𝒜 : GradedAlgebraSheaf 𝒪 ι} (M N : Mod(𝒜)) : Neg (Hom M N) where
  neg f :=
    { hom := fun n ↦ -f.hom n
      comm := sorry }

/-- Subtraction of graded-module morphisms is computed in every degree. -/
instance instSubHom {𝒜 : GradedAlgebraSheaf 𝒪 ι} (M N : Mod(𝒜)) : Sub (Hom M N) where
  sub f g :=
    { hom := fun n ↦ f.hom n - g.hom n
      comm := sorry }

/-- Natural scalar multiplication of graded-module morphisms is computed in every degree. -/
instance instSMulNatHom {𝒜 : GradedAlgebraSheaf 𝒪 ι} (M N : Mod(𝒜)) :
    SMul ℕ (Hom M N) where
  smul k f :=
    { hom := fun n ↦ k • f.hom n
      comm := sorry }

/-- Integer scalar multiplication of graded-module morphisms is computed in every degree. -/
instance instSMulIntHom {𝒜 : GradedAlgebraSheaf 𝒪 ι} (M N : Mod(𝒜)) :
    SMul ℤ (Hom M N) where
  smul k f :=
    { hom := fun n ↦ k • f.hom n
      comm := sorry }

/-- Graded-module morphisms inherit their additive commutative group from degreewise maps. -/
instance instAddCommGroupHom {𝒜 : GradedAlgebraSheaf 𝒪 ι} (M N : Mod(𝒜)) :
    AddCommGroup (Hom M N) :=
  Function.Injective.addCommGroup
    (fun f : Hom M N ↦ f.hom)
    hom_injective
    rfl
    (fun _ _ ↦ rfl)
    (fun _ ↦ rfl)
    (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl)

/-- The zero graded-module morphism has zero components. -/
@[simp]
theorem zero_hom {𝒜 : GradedAlgebraSheaf 𝒪 ι} (M N : Mod(𝒜)) (n : ι) :
    (0 : Hom M N).hom n = 0 := sorry

/-- Addition of graded-module morphisms adds their components. -/
@[simp]
theorem add_hom {𝒜 : GradedAlgebraSheaf 𝒪 ι} {M N : Mod(𝒜)}
    (f g : Hom M N) (n : ι) : (f + g).hom n = f.hom n + g.hom n := sorry

/-- Negation of a graded-module morphism negates its components. -/
@[simp]
theorem neg_hom {𝒜 : GradedAlgebraSheaf 𝒪 ι} {M N : Mod(𝒜)}
    (f : Hom M N) (n : ι) : (-f).hom n = -f.hom n := sorry

/-- Subtraction of graded-module morphisms subtracts their components. -/
@[simp]
theorem sub_hom {𝒜 : GradedAlgebraSheaf 𝒪 ι} {M N : Mod(𝒜)}
    (f g : Hom M N) (n : ι) : (f - g).hom n = f.hom n - g.hom n := sorry

/-- Natural scalar multiplication of a graded-module morphism scales its components. -/
@[simp]
theorem nsmul_hom {𝒜 : GradedAlgebraSheaf 𝒪 ι} {M N : Mod(𝒜)}
    (k : ℕ) (f : Hom M N) (n : ι) : (k • f).hom n = k • f.hom n := sorry

/-- Integer scalar multiplication of a graded-module morphism scales its components. -/
@[simp]
theorem zsmul_hom {𝒜 : GradedAlgebraSheaf 𝒪 ι} {M N : Mod(𝒜)}
    (k : ℤ) (f : Hom M N) (n : ι) : (k • f).hom n = k • f.hom n := sorry

/-- Graded module sheaves form a preadditive category with degreewise Hom operations. -/
instance instPreadditive (𝒜 : GradedAlgebraSheaf 𝒪 ι) : Preadditive (Mod(𝒜)) where
  homGroup M N := instAddCommGroupHom M N
  add_comp := sorry
  comp_add := sorry

end SheafOfModules.RingedSite.GradedModuleSheaf
