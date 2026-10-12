/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Additive
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module

/-!
# Preadditive differential graded module categories

The additive structure is transported from underlying cochain maps. The monoidal-preadditive
hypothesis is exactly what makes sums of action-compatible maps action-compatible.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

section


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {𝒪 : Sheaf J CommRingCat.{w}}
namespace DifferentialGradedModule

/-- Addition of differential graded module morphisms is computed on underlying cochain maps. -/
instance instAddHom {𝒜 : DGA(𝒪)} (M N : Mod(𝒜, d)) : Add (Hom M N) where
  add f g :=
    { toCochainMap := f.toCochainMap + g.toCochainMap
      comm := sorry }

/-- Negation of differential graded module morphisms is computed on underlying cochain maps. -/
instance instNegHom {𝒜 : DGA(𝒪)} (M N : Mod(𝒜, d)) : Neg (Hom M N) where
  neg f :=
    { toCochainMap := -f.toCochainMap
      comm := sorry }

/-- Subtraction of differential graded module morphisms is computed on underlying cochain maps. -/
instance instSubHom {𝒜 : DGA(𝒪)} (M N : Mod(𝒜, d)) : Sub (Hom M N) where
  sub f g :=
    { toCochainMap := f.toCochainMap - g.toCochainMap
      comm := sorry }

/-- Natural-number scalar multiplication is computed on underlying cochain maps. -/
instance instSMulNatHom {𝒜 : DGA(𝒪)} (M N : Mod(𝒜, d)) : SMul ℕ (Hom M N) where
  smul k f :=
    { toCochainMap := k • f.toCochainMap
      comm := sorry }

/-- Integer scalar multiplication is computed on underlying cochain maps. -/
instance instSMulIntHom {𝒜 : DGA(𝒪)} (M N : Mod(𝒜, d)) : SMul ℤ (Hom M N) where
  smul k f :=
    { toCochainMap := k • f.toCochainMap
      comm := sorry }

/-- The underlying cochain map of a sum is the sum of underlying cochain maps. -/
@[simp]
theorem add_toCochainMap {𝒜 : DGA(𝒪)} {M N : Mod(𝒜, d)} (f g : Hom M N) :
    (f + g).toCochainMap = f.toCochainMap + g.toCochainMap := sorry

/-- The underlying cochain map of a negated morphism is the negated cochain map. -/
@[simp]
theorem neg_toCochainMap {𝒜 : DGA(𝒪)} {M N : Mod(𝒜, d)} (f : Hom M N) :
    (-f).toCochainMap = -f.toCochainMap := sorry

/-- The underlying cochain map of a difference is the difference of the cochain maps. -/
@[simp]
theorem sub_toCochainMap {𝒜 : DGA(𝒪)} {M N : Mod(𝒜, d)} (f g : Hom M N) :
    (f - g).toCochainMap = f.toCochainMap - g.toCochainMap := sorry

/-- The underlying cochain map of a natural multiple is the corresponding natural multiple. -/
@[simp]
theorem nsmul_toCochainMap {𝒜 : DGA(𝒪)} {M N : Mod(𝒜, d)}
    (k : ℕ) (f : Hom M N) :
    (k • f).toCochainMap = k • f.toCochainMap := sorry

/-- The underlying cochain map of an integer multiple is the corresponding integer multiple. -/
@[simp]
theorem zsmul_toCochainMap {𝒜 : DGA(𝒪)} {M N : Mod(𝒜, d)}
    (k : ℤ) (f : Hom M N) :
    (k • f).toCochainMap = k • f.toCochainMap := sorry

/-- Differential graded module morphisms form an additive commutative group. -/
instance instAddCommGroupHom {𝒜 : DGA(𝒪)} (M N : Mod(𝒜, d)) :
    AddCommGroup (Hom M N) :=
  Function.Injective.addCommGroup
    (fun f : Hom M N ↦ f.toCochainMap)
    toCochainMap_injective
    sorry
    (fun _ _ ↦ sorry)
    (fun _ ↦ sorry)
    (fun _ _ ↦ sorry)
    (fun _ _ ↦ sorry)
    (fun _ _ ↦ sorry)

/-- Differential graded modules over a fixed algebra form a preadditive category. -/
instance instPreadditive (𝒜 : DGA(𝒪)) : Preadditive (Mod(𝒜, d)) where
  homGroup M N := instAddCommGroupHom M N
  add_comp := sorry
  comp_add := sorry

/-- Forgetting a differential graded module to its underlying cochain complex is additive. -/
instance forgetToComplex_additive (𝒜 : DGA(𝒪)) :
    (forgetToComplex 𝒜).Additive := sorry

end DifferentialGradedModule

end


end SheafOfModules.RingedSite
